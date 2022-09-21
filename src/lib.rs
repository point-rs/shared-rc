#![no_std]
#![cfg_attr(docsrs, feature(doc_auto_cfg))]

extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

/// A trait blanket implemented for *all* types.
///
/// Used as `dyn Destruct` to represent truly any type. [`Any`](core::any::Any)
/// introduces an undesired `'static` bound, [`Drop`] bounds test uselessly for
/// explicit `Drop` implementations, and [`Sized`] is not `dyn` safe, thus this
/// trait.
///
/// See also the unstable [`std::marker::Destruct`](core::marker::Destruct).
pub trait Destruct {}
impl<T: ?Sized> Destruct for T {}

pub use self::{rc::Rc, sync::Arc};
use core::{
    borrow::Borrow,
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    ops::Deref,
    ptr,
};
#[cfg(feature = "std")]
use std::{error::Error, panic::UnwindSafe};

macro_rules! make_shared_rc {
    ($Rc:ident) => {
        /// A projecting version of
        #[doc = concat!(" [`", stringify!($Rc), "`](rc::", stringify!($Rc), ")")]
        /// which allows owning a containing struct but referencing a field.
        #[derive(Clone)]
        pub struct $Rc<T: ?Sized, Owner: ?Sized = dyn Destruct> {
            owner: rc::$Rc<Owner>,
            this: ptr::NonNull<T>,
        }

        unsafe impl<T: ?Sized, Owner: ?Sized> Send for $Rc<T, Owner> where rc::$Rc<T>: Send {}
        unsafe impl<T: ?Sized, Owner: ?Sized> Sync for $Rc<T, Owner> where rc::$Rc<T>: Sync {}

        #[cfg(feature = "std")]
        impl<T: ?Sized, Owner: ?Sized> UnwindSafe for $Rc<T, Owner>
        where
            for<'a> &'a T: UnwindSafe,
            rc::$Rc<Owner>: UnwindSafe,
        {
        }

        /// A projecting version of
        /// [`Weak`](rc::Weak)
        /// which allows owning a containing struct but referencing a field.
        #[derive(Clone)]
        pub struct Weak<T: ?Sized, Owner: ?Sized = dyn Destruct> {
            owner: rc::Weak<Owner>,
            this: ptr::NonNull<T>,
        }

        unsafe impl<T: ?Sized, Owner: ?Sized> Send for Weak<T, Owner> where rc::Weak<T>: Send {}
        unsafe impl<T: ?Sized, Owner: ?Sized> Sync for Weak<T, Owner> where rc::Weak<T>: Sync {}

        #[cfg(feature = "std")]
        impl<T: ?Sized, Owner: ?Sized> UnwindSafe for Weak<T, Owner>
        where
            for<'a> &'a T: UnwindSafe,
            rc::Weak<Owner>: UnwindSafe,
        {
        }

        impl<'a, T: 'a> $Rc<T, dyn 'a + Destruct> {
            /// Constructs a new
            #[doc = concat!("`", stringify!($Rc), "<T>`")]
            /// .
            pub fn new(this: T) -> Self {
                $Rc::erase_owner($Rc::<T, T>::from(this))
            }
        }

        impl<'a, T: ?Sized, Owner: 'a + Sized> $Rc<T, Owner> {
            /// Erases the owning type so projected
            #[doc = stringify!($Rc)]
            /// can be used uniformly.
            pub fn erase_owner(this: Self) -> $Rc<T, dyn 'a + Destruct> {
                let Self { owner, this } = this;
                $Rc { owner, this }
            }
        }

        impl<T: ?Sized, Owner: ?Sized> $Rc<T, Owner> {
            /// Provides a raw pointer to the data.
            pub fn as_ptr(this: &Self) -> *const T {
                this.this.as_ptr()
            }

            /// Creates a new [`Weak`] pointer to this projected field.
            pub fn downgrade(this: &Self) -> Weak<T, Owner> {
                let &Self { ref owner, this } = this;
                let owner = rc::$Rc::downgrade(owner);
                Weak { owner, this }
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
            ) -> $Rc<U, Owner> {
                let Self { owner, this } = this;
                let this = projection(unsafe { this.as_ref() }).into();
                $Rc { owner, this }
            }

            /// Returns `true` if the two
            #[doc = concat!("`", stringify!($Rc), "`s")]
            /// point to the same allocation (in a vein similar to [`ptr::eq`]).
            pub fn ptr_eq(lhs: &Self, rhs: &Self) -> bool {
                rc::$Rc::ptr_eq(&lhs.owner, &rhs.owner) && lhs.this.as_ptr() == rhs.this.as_ptr()
            }
        }

        impl<T: ?Sized, Owner: ?Sized> AsRef<T> for $Rc<T, Owner> {
            fn as_ref(&self) -> &T {
                unsafe { self.this.as_ref() }
            }
        }

        impl<T: ?Sized, Owner: ?Sized> Borrow<T> for $Rc<T, Owner> {
            fn borrow(&self) -> &T {
                self.as_ref()
            }
        }

        #[cfg(feature = "unsize")]
        unsafe impl<T, U: ?Sized, Owner: ?Sized> unsize::CoerciblePtr<U> for $Rc<T, Owner> {
            type Pointee = T;
            type Output = $Rc<U, Owner>;

            fn as_sized_ptr(&mut self) -> *mut Self::Pointee {
                self.this.as_ptr()
            }

            unsafe fn replace_ptr(self, ptr: *mut U) -> Self::Output {
                $Rc {
                    owner: self.owner,
                    this: ptr::NonNull::new_unchecked(ptr),
                }
            }
        }

        #[cfg(feature = "unsize")]
        impl<T: ?Sized, Owner: ?Sized> $Rc<T, Owner> {
            /// Convert this pointer with an unsizing coercion
            /// (e.g. from `T` to `dyn Trait` or `[T; N]` to `[T]`).
            pub fn unsize<U: ?Sized, F>(
                this: Self,
                with: unsize::Coercion<T, U, F>,
            ) -> $Rc<U, Owner>
            where
                T: Sized,
                F: FnOnce(*const T) -> *const U,
            {
                use unsize::CoerceUnsize;
                let Self { owner, this } = this;
                let this = this.unsize(with);
                $Rc { owner, this }
            }

            /// Convert this pointer with an unsizing coercion of the owner
            /// (e.g. from `T` to `dyn Trait` or `[T; N]` to `[T]`).
            pub fn unsize_owner<Pwner: ?Sized, F>(
                this: Self,
                with: unsize::Coercion<Owner, Pwner, F>,
            ) -> $Rc<T, Pwner>
            where
                Owner: Sized,
                F: FnOnce(*const Owner) -> *const Pwner,
            {
                use unsize::CoerceUnsize;
                let Self { owner, this } = this;
                let owner = unsafe { rc::$Rc::from_raw(rc::$Rc::into_raw(owner).unsize(with)) };
                $Rc { owner, this }
            }
        }

        impl<T: ?Sized, Owner: ?Sized> fmt::Debug for $Rc<T, Owner>
        where
            T: fmt::Debug,
        {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Debug::fmt(&**self, f)
            }
        }

        impl<T: Default> Default for $Rc<T, T> {
            fn default() -> Self {
                Self::from(T::default())
            }
        }

        impl<T: 'static + Default> Default for $Rc<T> {
            fn default() -> Self {
                Self::new(T::default())
            }
        }

        impl<T: ?Sized, Owner: ?Sized> Deref for $Rc<T, Owner> {
            type Target = T;

            fn deref(&self) -> &T {
                self.as_ref()
            }
        }

        impl<T: ?Sized, Owner: ?Sized> fmt::Display for $Rc<T, Owner>
        where
            T: fmt::Display,
        {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Display::fmt(&**self, f)
            }
        }

        impl<T: ?Sized, Owner: ?Sized> Eq for $Rc<T, Owner> where T: Eq {}

        #[cfg(feature = "std")]
        impl<T: ?Sized, Owner: ?Sized> Error for $Rc<T, Owner>
        where
            T: Error,
        {
            fn source(&self) -> Option<&(dyn 'static + Error)> {
                Error::source(&**self)
            }
        }

        impl<T, Owner: ?Sized> From<T> for $Rc<T, Owner>
        where
            $Rc<T, Owner>: From<$Rc<T, T>>,
        {
            fn from(this: T) -> Self {
                $Rc::<T, T>::from(rc::$Rc::from(this)).into()
            }
        }

        impl<T: ?Sized> From<rc::$Rc<T>> for $Rc<T, T> {
            fn from(owner: rc::$Rc<T>) -> Self {
                let this = ptr::NonNull::new(rc::$Rc::as_ptr(&owner) as _).unwrap();
                $Rc { owner, this }
            }
        }

        impl<T: ?Sized, Owner: ?Sized> From<$Rc<T, Owner>> for rc::$Rc<Owner> {
            fn from(this: $Rc<T, Owner>) -> Self {
                this.owner
            }
        }

        impl<'a, T: ?Sized, Owner: 'a> From<$Rc<T, Owner>> for $Rc<T, dyn 'a + Destruct> {
            fn from(this: $Rc<T, Owner>) -> Self {
                let $Rc { owner, this } = this;
                $Rc { owner, this }
            }
        }

        impl<T: ?Sized, Owner: ?Sized> Hash for $Rc<T, Owner>
        where
            T: Hash,
        {
            fn hash<H: Hasher>(&self, state: &mut H) {
                Hash::hash(&**self, state)
            }
        }

        impl<T: ?Sized, Owner: ?Sized> Ord for $Rc<T, Owner>
        where
            T: Ord,
        {
            fn cmp(&self, other: &Self) -> Ordering {
                Ord::cmp(&**self, &**other)
            }
        }

        impl<T: ?Sized, Owner: ?Sized> PartialEq for $Rc<T, Owner>
        where
            T: PartialEq,
        {
            fn eq(&self, other: &Self) -> bool {
                PartialEq::eq(&**self, &**other)
            }
        }

        impl<T: ?Sized, Owner: ?Sized> PartialOrd for $Rc<T, Owner>
        where
            T: PartialOrd,
        {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                PartialOrd::partial_cmp(&**self, &**other)
            }
        }

        impl<T: ?Sized, Owner: ?Sized> fmt::Pointer for $Rc<T, Owner> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Pointer::fmt(&self.this, f)
            }
        }

        impl<'a, T: 'a> Weak<T, dyn 'a + Destruct> {
            /// Constructs a new `Weak<T>`
            pub fn new() -> Self {
                Weak::erase_owner(Weak::<T, T>::default())
            }
        }

        impl<'a, T: ?Sized, Owner: 'a + Sized> Weak<T, Owner> {
            pub fn erase_owner(this: Self) -> Weak<T, dyn 'a + Destruct> {
                let Self { owner, this } = this;
                Weak { owner, this }
            }
        }

        impl<T: ?Sized, Owner: ?Sized> Weak<T, Owner> {
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
                Some($Rc { owner, this })
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
            ) -> Weak<U, Owner> {
                let Self { owner, this } = this;
                let this = match owner.upgrade() {
                    None => ptr::NonNull::new(usize::MAX as *mut U).unwrap(),
                    Some(_guard) => projection(unsafe { this.as_ref() }).into(),
                };
                Weak { owner, this }
            }

            /// Returns `true` if the two `Weak`s point to the same allocation
            /// (similar to [`ptr::eq`]), or if both don't point to any
            /// allocation (because they were crated with `Weak::new()`).
            pub fn ptr_eq(lhs: &Self, rhs: &Self) -> bool {
                rc::Weak::ptr_eq(&lhs.owner, &rhs.owner) && lhs.this.as_ptr() == rhs.this.as_ptr()
            }
        }

        #[cfg(feature = "unsize")]
        unsafe impl<T, U: ?Sized, Owner: ?Sized> unsize::CoerciblePtr<U> for Weak<T, Owner> {
            type Pointee = T;
            type Output = Weak<U, Owner>;

            fn as_sized_ptr(&mut self) -> *mut Self::Pointee {
                self.this.as_ptr()
            }

            unsafe fn replace_ptr(self, ptr: *mut U) -> Self::Output {
                Weak {
                    owner: self.owner,
                    this: ptr::NonNull::new_unchecked(ptr),
                }
            }
        }

        #[cfg(feature = "unsize")]
        impl<T: ?Sized, Owner: ?Sized> Weak<T, Owner> {
            /// Convert this pointer with an unsizing coercion
            /// (e.g. from `T` to `dyn Trait` or `[T; N]` to `[T]`).
            pub fn unsize<U: ?Sized, F>(
                this: Self,
                with: unsize::Coercion<T, U, F>,
            ) -> Weak<U, Owner>
            where
                T: Sized,
                F: FnOnce(*const T) -> *const U,
            {
                use unsize::CoerceUnsize;
                let Self { owner, this } = this;
                let this = this.unsize(with);
                Weak { owner, this }
            }

            /// Convert this pointer with an unsizing coercion of the owner
            /// (e.g. from `T` to `dyn Trait` or `[T; N]` to `[T]`).
            pub fn unsize_owner<Pwner: ?Sized, F>(
                this: Self,
                with: unsize::Coercion<Owner, Pwner, F>,
            ) -> Weak<T, Pwner>
            where
                Owner: Sized,
                F: FnOnce(*const Owner) -> *const Pwner,
            {
                use unsize::CoerceUnsize;
                let Self { owner, this } = this;
                let owner = unsafe { rc::Weak::from_raw(rc::Weak::into_raw(owner).unsize(with)) };
                Weak { owner, this }
            }
        }

        impl<T: ?Sized, Owner: ?Sized> fmt::Debug for Weak<T, Owner>
        where
            T: fmt::Debug,
        {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "(Weak)")
            }
        }

        impl<T, Owner: ?Sized> Default for Weak<T, Owner>
        where
            Weak<T, Owner>: From<Weak<T, T>>,
        {
            fn default() -> Self {
                Self::from(Weak::<T, T> {
                    owner: rc::Weak::new(),
                    this: ptr::NonNull::new(usize::MAX as *mut T).unwrap(),
                })
            }
        }

        impl<'a, T: ?Sized, Owner: 'a> From<Weak<T, Owner>> for Weak<T, dyn 'a + Destruct> {
            fn from(this: Weak<T, Owner>) -> Self {
                let Weak { owner, this } = this;
                Weak { owner, this }
            }
        }
    };
}

/// Thread-safe reference-counting pointers.
///
/// See the [`Arc`] documentation for more details.
pub mod sync {
    use {super::*, alloc::sync as rc};
    make_shared_rc!(Arc);
}

/// Single-threaded reference-counting pointers.
///
/// See the [`Rc`] documentation for more details.
pub mod rc {
    use {super::*, alloc::rc};
    make_shared_rc!(Rc);
}
