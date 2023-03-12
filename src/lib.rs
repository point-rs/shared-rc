#![no_std]
#![cfg_attr(docsrs, feature(doc_auto_cfg))]

extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

/// A marker trait for types that can be dropped (*all* types).
///
/// Used as `dyn Destruct` to represent truly any type. [`Any`](core::any::Any)
/// introduces an undesired `'static` bound, [`Drop`] bounds test uselessly for
/// explicit `Drop` implementations, and [`Sized`] is not `dyn` safe, thus this
/// trait.
///
/// See also the unstable [`std::marker::Destruct`](core::marker::Destruct).
pub trait Destruct {}
impl<T: ?Sized> Destruct for T {}

use core::{
    borrow::Borrow,
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
    ops::Deref,
    ptr,
};
#[cfg(feature = "std")]
use std::error::Error;

type LocalOwner<'a> = dyn 'a + Destruct;
type GuestOwner<'a> = dyn 'a + Destruct + Send + Sync;

/// Alias for [`rc::Rc`] where `T: 'static`.
pub type Rc<T, Owner = LocalOwner<'static>> = crate::rc::Rc<'static, T, Owner>;
/// Alias for [`rc::Weak`] where `T: 'static`.
pub type WeakRc<T, Owner = LocalOwner<'static>> = crate::rc::Weak<'static, T, Owner>;
/// Alias for [`sync::Arc`] where `T: 'static`.
pub type Arc<T, Owner = GuestOwner<'static>> = crate::sync::Arc<'static, T, Owner>;
/// Alias for [`sync::Weak`] where `T: 'static`.
pub type WeakArc<T, Owner = GuestOwner<'static>> = crate::sync::Weak<'static, T, Owner>;

macro_rules! make_shared_strong {
    ($Rc:ident: $($Oibit:ident+)*) => {
        /// A projecting version of
        #[doc = concat!(" [`", stringify!($Rc), "`](rc::", stringify!($Rc), ")")]
        /// which allows owning a containing struct but referencing a field.
        ///
        /// The lifetime is an implied upper-bound (covariant) lifetime on
        /// the projected field type. This bound is necessary for soundness,
        /// but can be left as `'static` in most cases, where `T: 'static`.
        pub struct $Rc<'a, T: ?Sized, Owner: ?Sized = DynOwner<'a>> {
            owner: rc::$Rc<Owner>,
            this: ptr::NonNull<T>,
            marker: PhantomData<&'a T>,
        }

        // Send + Sync are impld outside the macro
        // implied UnwindSafe is correct

        impl<T: ?Sized, Owner: ?Sized> Clone for $Rc<'_, T, Owner> {
            fn clone(&self) -> Self {
                Self {
                    owner: self.owner.clone(),
                    this: self.this,
                    marker: self.marker,
                }
            }
        }

        impl<'a, T: 'a $(+$Oibit)*> $Rc<'_, T, DynOwner<'a>> {
            /// Constructs a new
            #[doc = concat!("`", stringify!($Rc), "<T>`")]
            /// with erased owner.
            pub fn new(this: T) -> Self {
                $Rc::erase_owner($Rc::new_owner(this))
            }
        }

        impl<T> $Rc<'_, T, T> {
            /// Constructs a new
            #[doc = concat!("`", stringify!($Rc), "<T, T>`")]
            /// with typed owner.
            pub fn new_owner(this: T) -> Self {
                Self::from(this)
            }
        }

        impl<'a, 'o, T: ?Sized, Owner: 'o $(+$Oibit)*> $Rc<'a, T, Owner> {
            /// Erases the owning type so projected
            #[doc = concat!("`", stringify!($Rc), "<T>`")]
            /// can be used uniformly.
            pub fn erase_owner(this: Self) -> $Rc<'a, T, DynOwner<'o>> {
                let Self { owner, this, marker } = this;
                $Rc { owner, this, marker }
            }
        }

        impl<'a, T: ?Sized, Owner: ?Sized> $Rc<'a, T, Owner> {
            /// Provides a raw pointer to the data.
            pub fn as_ptr(this: &Self) -> *const T {
                this.this.as_ptr()
            }

            /// Creates a new [`Weak`] pointer to this projected field.
            pub fn downgrade(this: &Self) -> Weak<T, Owner> {
                let &Self { ref owner, this, marker } = this;
                let owner = rc::$Rc::downgrade(owner);
                Weak { owner, this, marker }
            }

            /// Gets a reference to the owning allocation.
            ///
            /// This returns a clone of the owning
            #[doc = concat!("`", stringify!($Rc), "`,")]
            /// so it cannot return a unique reference. If you want to take
            /// unique ownership, use [`into_owner`](Self::into_owner) instead.
            pub fn owner(this: &Self) -> rc::$Rc<Owner> {
                rc::$Rc::clone(&this.owner)
            }

            /// Consumes this projected field and returns the owning allocation.
            pub fn into_owner(this: Self) -> rc::$Rc<Owner> {
                this.owner
            }

            /// Projects this allocation to a field.
            ///
            /// Note that the projected field is ***not*** required to actually
            /// be owned by the owner; it could be any longer-lived reference.
            pub fn project<U: ?Sized>(
                this: Self,
                projection: impl FnOnce(&T) -> &U,
            ) -> $Rc<'a, U, Owner> {
                let Self { owner, this, .. } = this;
                let this = projection(unsafe { this.as_ref() }).into();
                $Rc { owner, this, marker: PhantomData }
            }

            /// Returns `true` if the two
            #[doc = concat!("`", stringify!($Rc), "`s")]
            /// point to the same field in the same allocated object.
            ///
            /// See [`ptr::eq`] for the caveats when comparing `dyn Trait`
            /// pointers, which this does when the owner type is erased.
            pub fn ptr_eq(lhs: &Self, rhs: &Self) -> bool {
                true
                && rc::$Rc::ptr_eq(&lhs.owner, &rhs.owner)
                && lhs.this.as_ptr() == rhs.this.as_ptr()
            }
        }

        impl<T: ?Sized, Owner: ?Sized> AsRef<T> for $Rc<'_, T, Owner> {
            fn as_ref(&self) -> &T {
                unsafe { self.this.as_ref() }
            }
        }

        impl<T: ?Sized, Owner: ?Sized> Borrow<T> for $Rc<'_, T, Owner> {
            fn borrow(&self) -> &T {
                self.as_ref()
            }
        }

        #[cfg(feature = "unsize")]
        unsafe impl<'a, T, U: 'a + ?Sized, Owner: ?Sized> unsize::CoerciblePtr<U> for $Rc<'a, T, Owner> {
            type Pointee = T;
            type Output = $Rc<'a, U, Owner>;

            fn as_sized_ptr(&mut self) -> *mut Self::Pointee {
                self.this.as_ptr()
            }

            unsafe fn replace_ptr(self, ptr: *mut U) -> Self::Output {
                $Rc {
                    owner: self.owner,
                    this: ptr::NonNull::new_unchecked(ptr),
                    marker: PhantomData,
                }
            }
        }

        #[cfg(feature = "unsize")]
        impl<'a, T: ?Sized, Owner: ?Sized> $Rc<'a, T, Owner> {
            /// Convert this pointer with an unsizing coercion
            /// (e.g. from `T` to `dyn Trait` or `[T; N]` to `[T]`).
            pub fn unsize<U: ?Sized, F>(
                this: Self,
                with: unsize::Coercion<T, U, F>,
            ) -> $Rc<'a, U, Owner>
            where
                T: Sized,
                F: FnOnce(*const T) -> *const U,
            {
                use unsize::CoerceUnsize;
                let Self { owner, this, .. } = this;
                let this = this.unsize(with);
                $Rc { owner, this, marker: PhantomData }
            }

            /// Convert this pointer with an unsizing coercion of the owner
            /// (e.g. from `T` to `dyn Trait` or `[T; N]` to `[T]`).
            pub fn unsize_owner<Pwner: ?Sized, F>(
                this: Self,
                with: unsize::Coercion<Owner, Pwner, F>,
            ) -> $Rc<'a, T, Pwner>
            where
                Owner: Sized,
                F: FnOnce(*const Owner) -> *const Pwner,
            {
                use unsize::CoerceUnsize;
                let Self { owner, this, marker } = this;
                let owner = unsafe { rc::$Rc::from_raw(rc::$Rc::into_raw(owner).unsize(with)) };
                $Rc { owner, this, marker }
            }
        }

        impl<T: ?Sized, Owner: ?Sized> fmt::Debug for $Rc<'_, T, Owner>
        where
            T: fmt::Debug,
        {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Debug::fmt(&**self, f)
            }
        }

        impl<T: Default> Default for $Rc<'_, T, T> {
            fn default() -> Self {
                Self::from(T::default())
            }
        }

        impl<'o, T: 'o + Default> Default for $Rc<'_, T, dyn 'o + Destruct> {
            fn default() -> Self {
                let $Rc { owner, this, marker } = $Rc::<T, T>::default();
                Self { owner, this, marker }
            }
        }

        impl<'o, T: 'o + Default + Send> Default for $Rc<'_, T, dyn 'o + Destruct + Send> {
            fn default() -> Self {
                let $Rc { owner, this, marker } = $Rc::<T, T>::default();
                Self { owner, this, marker }
            }
        }

        impl<'o, T: 'o + Default + Send + Sync> Default for $Rc<'_, T, dyn 'o + Destruct + Send + Sync> {
            fn default() -> Self {
                let $Rc { owner, this, marker } = $Rc::<T, T>::default();
                Self { owner, this, marker }
            }
        }

        impl<T: ?Sized, Owner: ?Sized> Deref for $Rc<'_, T, Owner> {
            type Target = T;

            fn deref(&self) -> &T {
                self.as_ref()
            }
        }

        impl<T: ?Sized, Owner: ?Sized> fmt::Display for $Rc<'_, T, Owner>
        where
            T: fmt::Display,
        {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Display::fmt(&**self, f)
            }
        }

        impl<T: ?Sized, Owner: ?Sized> Eq for $Rc<'_, T, Owner> where T: Eq {}

        #[cfg(feature = "std")]
        impl<T: ?Sized, Owner: ?Sized> Error for $Rc<'_, T, Owner>
        where
            T: Error,
        {
            fn source(&self) -> Option<&(dyn 'static + Error)> {
                Error::source(&**self)
            }
        }

        impl<'a, T, Owner: ?Sized> From<T> for $Rc<'a, T, Owner>
        where
            $Rc<'a, T, Owner>: From<$Rc<'a, T, T>>,
        {
            fn from(this: T) -> Self {
                $Rc::<T, T>::from(rc::$Rc::from(this)).into()
            }
        }

        impl<T: ?Sized> From<rc::$Rc<T>> for $Rc<'_, T, T> {
            fn from(owner: rc::$Rc<T>) -> Self {
                let this = ptr::NonNull::new(rc::$Rc::as_ptr(&owner) as *mut T)
                    .unwrap();
                $Rc { owner, this, marker: PhantomData }
            }
        }

        impl<T: ?Sized, Owner: ?Sized> From<$Rc<'_, T, Owner>> for rc::$Rc<Owner> {
            fn from(this: $Rc<T, Owner>) -> Self {
                this.owner
            }
        }

        impl<'a, 'o, T: ?Sized, Owner: 'o> From<$Rc<'a, T, Owner>>
        for $Rc<'a, T, dyn 'o + Destruct> {
            fn from(this: $Rc<'a, T, Owner>) -> Self {
                let $Rc { owner, this, marker } = this;
                $Rc { owner, this, marker }
            }
        }

        impl<'a, 'o, T: ?Sized, Owner: 'o + Send> From<$Rc<'a, T, Owner>>
        for $Rc<'a, T, dyn 'o + Destruct + Send> {
            fn from(this: $Rc<'a, T, Owner>) -> Self {
                let $Rc { owner, this, marker } = this;
                $Rc { owner, this, marker }
            }
        }


        impl<'a, 'o, T: ?Sized, Owner: 'o + Send + Sync> From<$Rc<'a, T, Owner>>
        for $Rc<'a, T, dyn 'o + Destruct + Send + Sync> {
            fn from(this: $Rc<'a, T, Owner>) -> Self {
                let $Rc { owner, this, marker } = this;
                $Rc { owner, this, marker }
            }
        }

        impl<T: ?Sized, Owner: ?Sized> Hash for $Rc<'_, T, Owner>
        where
            T: Hash,
        {
            fn hash<H: Hasher>(&self, state: &mut H) {
                Hash::hash(&**self, state)
            }
        }

        impl<T: ?Sized, Owner: ?Sized> Ord for $Rc<'_, T, Owner>
        where
            T: Ord,
        {
            fn cmp(&self, other: &Self) -> Ordering {
                Ord::cmp(&**self, &**other)
            }
        }

        impl<T: ?Sized, Owner: ?Sized> PartialEq for $Rc<'_, T, Owner>
        where
            T: PartialEq,
        {
            fn eq(&self, other: &Self) -> bool {
                PartialEq::eq(&**self, &**other)
            }
        }

        impl<T: ?Sized, Owner: ?Sized> PartialOrd for $Rc<'_, T, Owner>
        where
            T: PartialOrd,
        {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                PartialOrd::partial_cmp(&**self, &**other)
            }
        }

        impl<T: ?Sized, Owner: ?Sized> fmt::Pointer for $Rc<'_, T, Owner> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Pointer::fmt(&self.this, f)
            }
        }
    };
}

macro_rules! make_shared_weak {
    ($Rc:ident: $($Oibit:ident+)*) => {
        /// A projecting version of
        /// [`Weak`](rc::Weak)
        /// which allows owning a containing struct but referencing a field.
        pub struct Weak<'a, T: ?Sized, Owner: ?Sized = DynOwner<'a>> {
            owner: rc::Weak<Owner>,
            this: ptr::NonNull<T>,
            marker: PhantomData<&'a T>,
        }

        // Send + Sync are impld outside the macro
        // implied UnwindSafe is correct

        impl<T: ?Sized, Owner: ?Sized> Clone for Weak<'_, T, Owner> {
            fn clone(&self) -> Self {
                Self {
                    owner: self.owner.clone(),
                    this: self.this,
                    marker: self.marker,
                }
            }
        }

        impl<'o, T: 'o $(+$Oibit)*> Weak<'_, T, DynOwner<'o>> {
            /// Constructs a new
            /// `Weak<T>`
            /// with erased owner.
            pub fn new() -> Self {
                Weak::erase_owner(Weak::<T, T>::new_owner())
            }
        }

        impl<T, Owner> Weak<'_, T, Owner> {
            /// Constructs a new
            /// `Weak<T, T>`
            /// with typed owner.
            pub fn new_owner() -> Self {
                Self {
                    owner: rc::Weak::new(),
                    this: ptr::NonNull::dangling(),
                    marker: PhantomData,
                }
            }
        }

        impl<'a, 'o, T: ?Sized, Owner: 'o $(+$Oibit)*> Weak<'a, T, Owner> {
            /// Erases the owning type so that projected
            /// `Weak<T>`
            /// can be used uniformly.
            pub fn erase_owner(this: Self) -> Weak<'a, T, DynOwner<'o>> {
                let Self { owner, this, marker } = this;
                Weak { owner, this, marker }
            }
        }

        impl<'a, T: ?Sized, Owner: ?Sized> Weak<'a, T, Owner> {
            /// Returns a raw pointer to the object `T` pointed to by this
            /// `Weak<T>`.
            ///
            /// The pointer is valid only if there are some strong references.
            /// The pointer may be dangling, unaligned, or even null otherwise.
            pub fn as_ptr(&self) -> *const T {
                self.this.as_ptr()
            }

            /// Attempts to upgrade the `Weak` pointer to
            #[doc = concat!("`", stringify!($Rc), "<T>`.")]
            ///
            /// Returns [`None`] if no strong references exist.
            pub fn upgrade(&self) -> Option<$Rc<T, Owner>> {
                let owner = self.owner.upgrade()?;
                let this = self.this;
                Some($Rc { owner, this, marker: PhantomData })
            }

            /// Gets a reference to the owning allocation.
            pub fn owner(this: &Self) -> rc::Weak<Owner> {
                rc::Weak::clone(&this.owner)
            }

            /// Consumes this projected field, returning the owning allocation.
            pub fn into_owner(this: Self) -> rc::Weak<Owner> {
                this.owner
            }

            /// Projects this allocation to a field.
            ///
            /// If no strong references exist, the closure will not be called.
            pub fn project<U: Sized>(
                this: Self,
                projection: impl FnOnce(&T) -> &U,
            ) -> Weak<'a, U, Owner> {
                let Self { owner, this, .. } = this;
                let this = match owner.upgrade() {
                    None => ptr::NonNull::dangling(),
                    Some(_guard) => projection(unsafe { this.as_ref() }).into(),
                };
                Weak { owner, this, marker: PhantomData }
            }

            /// Returns `true` if the two `Weak`s point to the same field in
            /// the same allocated object, or if both don't point to anything
            /// (i.e. because they were created with `Weak::new()`).
            ///
            /// See [`ptr::eq`] for the caveats when comparing `dyn Trait`
            /// pointers, which this does when the owner type is erased.
            pub fn ptr_eq(lhs: &Self, rhs: &Self) -> bool {
                true
                && rc::Weak::ptr_eq(&lhs.owner, &rhs.owner)
                && lhs.this.as_ptr() == rhs.this.as_ptr()
            }
        }

        #[cfg(feature = "unsize")]
        unsafe impl<'a, T, U: 'a + ?Sized, Owner: ?Sized> unsize::CoerciblePtr<U> for Weak<'a, T, Owner> {
            type Pointee = T;
            type Output = Weak<'a, U, Owner>;

            fn as_sized_ptr(&mut self) -> *mut Self::Pointee {
                self.this.as_ptr()
            }

            unsafe fn replace_ptr(self, ptr: *mut U) -> Self::Output {
                Weak {
                    owner: self.owner,
                    this: ptr::NonNull::new_unchecked(ptr),
                    marker: PhantomData,
                }
            }
        }

        #[cfg(feature = "unsize")]
        impl<'a, T: ?Sized, Owner: ?Sized> Weak<'a, T, Owner> {
            /// Convert this pointer with an unsizing coercion
            /// (e.g. from `T` to `dyn Trait` or `[T; N]` to `[T]`).
            pub fn unsize<U: ?Sized, F>(
                this: Self,
                with: unsize::Coercion<T, U, F>,
            ) -> Weak<'a, U, Owner>
            where
                T: Sized,
                F: FnOnce(*const T) -> *const U,
            {
                use unsize::CoerceUnsize;
                let Self { owner, this, .. } = this;
                let this = this.unsize(with);
                Weak { owner, this, marker: PhantomData }
            }

            /// Convert this pointer with an unsizing coercion of the owner
            /// (e.g. from `T` to `dyn Trait` or `[T; N]` to `[T]`).
            pub fn unsize_owner<Pwner: ?Sized, F>(
                this: Self,
                with: unsize::Coercion<Owner, Pwner, F>,
            ) -> Weak<'a, T, Pwner>
            where
                Owner: Sized,
                F: FnOnce(*const Owner) -> *const Pwner,
            {
                use unsize::CoerceUnsize;
                let Self { owner, this, marker } = this;
                let owner = unsafe { rc::Weak::from_raw(rc::Weak::into_raw(owner).unsize(with)) };
                Weak { owner, this, marker }
            }
        }

        impl<T: ?Sized, Owner: ?Sized> fmt::Debug for Weak<'_, T, Owner>
        where
            T: fmt::Debug,
        {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "(Weak)")
            }
        }

        impl<T, Owner> Default for Weak<'_, T, Owner>
        {
            fn default() -> Self {
                Self {
                    owner: rc::Weak::new(),
                    this: ptr::NonNull::dangling(),
                    marker: PhantomData,
                }
            }
        }

        impl<'o, T: 'o> Default for Weak<'_, T, dyn 'o + Destruct>
        {
            fn default() -> Self {
                Self {
                    owner: rc::Weak::<()>::new(),
                    this: ptr::NonNull::dangling(),
                    marker: PhantomData,
                }
            }
        }

        impl<'o, T: 'o> Default for Weak<'_, T, dyn 'o + Destruct + Send>
        {
            fn default() -> Self {
                Self {
                    owner: rc::Weak::<()>::new(),
                    this: ptr::NonNull::dangling(),
                    marker: PhantomData,
                }
            }
        }

        impl<'o, T: 'o> Default for Weak<'_, T, dyn 'o + Destruct + Send + Sync>
        {
            fn default() -> Self {
                Self {
                    owner: rc::Weak::<()>::new(),
                    this: ptr::NonNull::dangling(),
                    marker: PhantomData,
                }
            }
        }

        impl<T> From<rc::Weak<T>> for Weak<'_, T, T> {
            fn from(owner: rc::Weak<T>) -> Self {
                let this = ptr::NonNull::new(owner.as_ptr() as *mut T)
                    .unwrap_or(ptr::NonNull::dangling());
                Self { owner, this, marker: PhantomData }
            }
        }

        impl<T: ?Sized, Owner: ?Sized> From<Weak<'_, T, Owner>> for rc::Weak<Owner> {
            fn from(this: Weak<T, Owner>) -> Self {
                this.owner
            }
        }

        impl<'a, 'o, T: ?Sized, Owner: 'o> From<Weak<'a, T, Owner>>
        for Weak<'a, T, dyn 'o + Destruct> {
            fn from(this: Weak<'a, T, Owner>) -> Self {
                let Weak { owner, this, marker } = this;
                Weak { owner, this, marker }
            }
        }

        impl<'a, 'o, T: ?Sized, Owner: 'o + Send> From<Weak<'a, T, Owner>>
        for Weak<'a, T, dyn 'o + Destruct + Send> {
            fn from(this: Weak<'a, T, Owner>) -> Self {
                let Weak { owner, this, marker } = this;
                Weak { owner, this, marker }
            }
        }

        impl<'a, 'o, T: ?Sized, Owner: 'o + Send + Sync> From<Weak<'a, T, Owner>>
        for Weak<'a, T, dyn 'o + Destruct + Send + Sync> {
            fn from(this: Weak<'a, T, Owner>) -> Self {
                let Weak { owner, this, marker } = this;
                Weak { owner, this, marker }
            }
        }
    };
}

macro_rules! make_shared_rc {
    ($Rc:ident: $($Oibit:ident+)*) => {
        make_shared_strong!($Rc: $($Oibit+)*);
        make_shared_weak!($Rc: $($Oibit+)*);
    };
}

/// Thread-safe reference-counting pointers.
///
/// See the [`Arc`] documentation for more details.
pub mod sync {
    use {super::GuestOwner as DynOwner, super::*, alloc::sync as rc};
    make_shared_rc!(Arc: Send+Sync+);

    unsafe impl<T: ?Sized, Owner: ?Sized> Send for Arc<'_, T, Owner>
    where
        Owner: Send + Sync,
        T: Sync,
    {
    }

    unsafe impl<'a, T: ?Sized, Owner: ?Sized> Sync for Arc<'a, T, Owner>
    where
        Owner: Send + Sync,
        T: Sync,
    {
    }

    unsafe impl<T: ?Sized, Owner: ?Sized> Send for Weak<'_, T, Owner>
    where
        Owner: Send + Sync,
        T: Sync,
    {
    }

    unsafe impl<'a, T: ?Sized, Owner: ?Sized> Sync for Weak<'a, T, Owner>
    where
        Owner: Send + Sync,
        T: Sync,
    {
    }
}

/// Single-threaded reference-counting pointers.
///
/// See the [`Rc`] documentation for more details.
pub mod rc {
    use {super::LocalOwner as DynOwner, super::*, alloc::rc};
    make_shared_rc!(Rc:);
}

/// Compile-fail tests.
///
/// Issue point-rs/shared-rc#3, a UAF unsoundness exploit. In short, `project`'s
/// `fn(&T) -> &U` lacked a requirement that the `&U` lives long enough. This is
/// now handled by phantom data telling borrowck to treat `Rc<'_, T>` like `&T`.
///
/// ```rust,compile_fail
/// # use shared_rc::rc::Rc;
/// let x = Rc::new_owner(());
/// let z: Rc<str, ()>;
/// {
///     let s = "Hello World!".to_string();
///     let s_ref: &str = &s;
///     let y: Rc<&str, ()> = Rc::project(x, |_| &s_ref);
///     z = Rc::project(y, |s: &&str| *s);
///     // s deallocated here
/// }
/// println!("{}", &*z); // printing garbage, accessing `s` after it’s freed
/// ```
const _: () = ();
