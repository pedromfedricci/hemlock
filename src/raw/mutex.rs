use core::fmt::{self, Debug, Display, Formatter};
use core::marker::PhantomData;
use core::ptr;
use core::sync::atomic::Ordering::{AcqRel, Acquire, Relaxed, Release};

use crate::cfg::atomic::{fence, AtomicPtr, AtomicPtrNull, AtomicUsize};
use crate::cfg::cell::{Cell, UnsafeCell, UnsafeCellOptionWith, UnsafeCellWith};
use crate::relax::Relax;

#[cfg(test)]
use crate::test::{LockNew, LockThen, LockWithThen, TryLockThen, TryLockWithThen};

/// Asserts that a node has its lock pointer set to `null`.
///
/// Useful to check this invariant prior to adding the node to the queue.
#[cfg(test)]
#[track_caller]
fn debug_assert_node(node: &MutexNode) {
    use core::panic::Location;
    const MSG: &str = "node's lock address was expected to be `null` at:";
    let location = Location::caller();
    let grant = node.grant.load(Relaxed);
    debug_assert_eq!(grant, 0, "{MSG} {location}");
}

/// Calls `debug_assert_node` over a target node under test profile only.
macro_rules! debug_assert_node {
    ($node:ident) => {
        #[cfg(test)]
        debug_assert_node($node);
    };
}

#[derive(Debug)]
pub struct MutexNode {
    grant: AtomicUsize,
    // Even though a mutex node is safe to be `Sync`, a multithreaded shared
    // node will result in deadlocks in anything but very simple locking use
    // cases.
    marker: PhantomData<Cell<()>>,
}

impl MutexNode {
    /// Creates new, empty `MutexNode` instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use hemlocker::raw::MutexNode;
    ///
    /// let node = MutexNode::new();
    /// ```
    #[cfg(not(all(loom, test)))]
    #[must_use]
    pub const fn new() -> Self {
        let grant = AtomicUsize::new(0);
        Self { grant, marker: PhantomData }
    }

    /// Creates new, empty and loom based `MutexNode` instance (non-const).
    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    #[must_use]
    pub fn new() -> Self {
        let grant = AtomicUsize::new(0);
        Self { grant, marker: PhantomData }
    }

    /// Returns a raw mutable pointer of this node.
    const fn as_ptr(&self) -> *mut Self {
        (self as *const Self).cast_mut()
    }

    /// A busy-wait loop that returns once the head is notified by a successor
    /// that they've acknowledged the lock ownership transfer.
    ///
    /// The successor notifies the lock transfer by setting the head's grant to
    /// `null`. The grant value is checked through a relaxed load.
    fn wait_acknowledgment_relaxed<R: Relax>(&self) {
        let mut relax = R::new();
        while self.grant.fetch_add(0, Relaxed) != 0 {
            relax.relax();
        }
    }

    /// A busy-wait loop that returns once the predecessor transfers the target
    /// lock ownership to the current thread.
    ///
    /// The predecessor node is notified of the lock ownership transfer by
    /// having its node's grant set to `null` through a release store.
    fn wait_transfer_release<T: ?Sized, R: Relax>(&self, lock: *const Mutex<T, R>) {
        let lock = Mutex::addr(lock);
        let mut relax = R::new();
        while self.grant.compare_exchange(lock, 0, Release, Relaxed).is_err() {
            relax.relax();
        }
    }
}

#[cfg(not(tarpaulin_include))]
impl Default for MutexNode {
    #[inline(always)]
    fn default() -> Self {
        Self::new()
    }
}

pub struct Mutex<T: ?Sized, R> {
    tail: AtomicPtr<MutexNode>,
    relax: PhantomData<R>,
    data: UnsafeCell<T>,
}

// Same unsafe impls as `std::sync::Mutex`.
unsafe impl<T: ?Sized + Send, R> Send for Mutex<T, R> {}
unsafe impl<T: ?Sized + Send, R> Sync for Mutex<T, R> {}

impl<T, R> Mutex<T, R> {
    #[cfg(not(all(loom, test)))]
    pub const fn new(value: T) -> Self {
        let tail = AtomicPtr::NULL_MUT;
        let data = UnsafeCell::new(value);
        Self { tail, data, relax: PhantomData }
    }

    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    pub fn new(value: T) -> Self {
        let tail = AtomicPtr::null_mut();
        let data = UnsafeCell::new(value);
        Self { tail, data, relax: PhantomData }
    }

    pub fn into_inner(self) -> T {
        self.data.into_inner()
    }
}

impl<T: ?Sized, R: Relax> Mutex<T, R> {
    /// Attempts to acquire this mutex and then runs a closure against the
    /// proteced data.
    ///
    /// If the lock could not be acquired at this time, then [`None`] is returned.
    /// Otherwise, an [`Some`] with a `&mut T` is returned. The lock will be
    /// unlocked once the closure goes out of scope.
    ///
    /// This function transparently allocates a [`MutexNode`] in the stack for
    /// each call, and so it will not reuse the same node for other calls.
    /// Consider callig [`try_lock_with_then`] if you want to reuse node
    /// allocations.
    ///
    /// This function does not block.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use hemlocker::raw;
    /// use hemlocker::relax::Spin;
    ///
    /// type Mutex<T> = raw::Mutex<T, Spin>;
    ///
    /// let mutex = Arc::new(Mutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || {
    ///     c_mutex.try_lock_then(|data| {
    ///         if let Some(data) = data {
    ///             *data = 10;
    ///         } else {
    ///             println!("try_lock failed");
    ///         }
    ///     });
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// let value = mutex.lock_then(|data| *data);
    /// assert_eq!(value, 10);
    /// ```
    ///
    /// Compile fail: borrows of the data cannot escape the given closure:
    ///
    /// ```compile_fail,E0515
    /// use hemlocker::raw::spins::Mutex;
    ///
    /// let mutex = Mutex::new(1);
    /// let borrow = mutex.try_lock_then(|data| &*data.unwrap());
    /// ```
    /// [`try_lock_with_then`]: Mutex::try_lock_with_then
    #[inline]
    pub fn try_lock_then<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<&mut T>) -> Ret,
    {
        self.try_lock_with_then(&MutexNode::new(), f)
    }

    /// Attempts to acquire this mutex and then runs a closure against the
    /// protected data.
    ///
    /// If the lock could not be acquired at this time, then [`None`] is returned.
    /// Otherwise, an [`Some`] with a `&mut T` is returned. The lock will be
    /// unlocked once the closure goes out of scope.
    ///
    /// To acquire a Hemlock through this function, it's also required to borrow
    /// from a queue node, which is a record that keeps a link for forming the
    /// queue, see [`MutexNode`].
    ///
    /// This function does not block.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use hemlocker::raw::{self, MutexNode};
    /// use hemlocker::relax::Spin;
    ///
    /// type Mutex<T> = raw::Mutex<T, Spin>;
    ///
    /// let mutex = Arc::new(Mutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || {
    ///     let node = MutexNode::new();
    ///     c_mutex.try_lock_with_then(&node, |data| {
    ///         if let Some(data) = data {
    ///             *data = 10;
    ///         } else {
    ///             println!("try_lock failed");
    ///         }
    ///     });
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// let node = MutexNode::new();
    /// let value = mutex.lock_with_then(&node, |data| *data);
    /// assert_eq!(value, 10);
    /// ```
    ///
    /// Compile fail: borrows of the data cannot escape the given closure:
    ///
    /// ```compile_fail,E0515
    /// use hemlocker::raw::{spins::Mutex, MutexNode};
    ///
    /// let mutex = Mutex::new(1);
    /// let node = MutexNode::new();
    /// let borrow = mutex.try_lock_with_then(&node, |data| &*data.unwrap());
    /// ```
    #[inline]
    pub fn try_lock_with_then<F, Ret>(&self, node: &MutexNode, f: F) -> Ret
    where
        F: FnOnce(Option<&mut T>) -> Ret,
    {
        // SAFETY: The guard's `drop` call is executed within this scope.
        unsafe { self.try_lock_with(node) }.as_deref_mut_with_mut(f)
    }

    /// Acquires this mutex and then runs the closure against the protected data.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon acquiring the mutex, the user provided closure will be
    /// executed against the mutex proteced data. Once the closure goes out of
    /// scope, it will unlock the mutex.
    ///
    /// This function transparently allocates a [`MutexNode`] in the stack for
    /// each call, and so it will not reuse the same node for other calls.
    /// Consider callig [`lock_with_then`] if you want to reuse node
    /// allocations.
    ///
    /// This function will block if the lock is unavailable.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use hemlocker::raw;
    /// use hemlocker::relax::Spin;
    ///
    /// type Mutex<T> = raw::Mutex<T, Spin>;
    ///
    /// let mutex = Arc::new(Mutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || {
    ///     c_mutex.lock_then(|data| *data = 10);
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// assert_eq!(mutex.lock_then(|data| *data), 10);
    /// ```
    ///
    /// Compile fail: borrows of the data cannot escape the given closure:
    ///
    /// ```compile_fail,E0515
    /// use hemlocker::raw::spins::Mutex;
    ///
    /// let mutex = Mutex::new(1);
    /// let borrow = mutex.lock_then(|data| &*data);
    /// ```
    /// [`lock_with_then`]: Mutex::lock_with_then
    #[inline]
    pub fn lock_then<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(&mut T) -> Ret,
    {
        self.lock_with_then(&MutexNode::new(), f)
    }

    /// Acquires this mutex and then runs the closure against the proteced data.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon acquiring the mutex, the user provided closure will be
    /// executed against the mutex proteced data. Once the closure goes out of
    /// scope, it will unlock the mutex.
    ///
    /// To acquire a Hemlock through this function, it's also required to borrow
    /// from a queue node, which is a record that keeps a link for forming the
    /// queue, see [`MutexNode`].
    ///
    /// This function will block if the lock is unavailable.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use hemlocker::raw::{self, MutexNode};
    /// use hemlocker::relax::Spin;
    ///
    /// type Mutex<T> = raw::Mutex<T, Spin>;
    ///
    /// let mutex = Arc::new(Mutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || {
    ///     let node = MutexNode::new();
    ///     c_mutex.lock_with_then(&node, |data| *data = 10);
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// let node = MutexNode::new();
    /// assert_eq!(mutex.lock_with_then(&node, |data| *data), 10);
    /// ```
    ///
    /// Compile fail: borrows of the data cannot escape the given closure:
    ///
    /// ```compile_fail,E0515
    /// use hemlocker::raw::{spins::Mutex, MutexNode};
    ///
    /// let mutex = Mutex::new(1);
    /// let node = MutexNode::new();
    /// let borrow = mutex.lock_with_then(&node, |data| &*data);
    /// ```
    #[inline]
    pub fn lock_with_then<F, Ret>(&self, node: &MutexNode, f: F) -> Ret
    where
        F: FnOnce(&mut T) -> Ret,
    {
        // SAFETY: The guard's `drop` call is executed within this scope.
        unsafe { self.lock_with(node) }.with_mut(f)
    }
}

impl<T: ?Sized, R: Relax> Mutex<T, R> {
    /// Attempts to acquire this mutex without blocking the thread.
    ///
    /// # Safety
    ///
    /// The returned guard instance **must** be dropped, that is, it **must not**
    /// be "forgotten" (e.g. `core::mem::forget`), or being targeted by any
    /// other operation that would prevent it from executing its `drop` call.
    unsafe fn try_lock_with<'a>(&'a self, node: &'a MutexNode) -> Option<MutexGuard<'a, T, R>> {
        debug_assert_node!(node);
        self.tail
            .compare_exchange(ptr::null_mut(), node.as_ptr(), AcqRel, Relaxed)
            .map(|_| MutexGuard::new(self, node))
            .ok()
    }

    /// Acquires this mutex, blocking the current thread until it is able to do so.
    ///
    /// # Safety
    ///
    /// The returned guard instance **must** be dropped, that is, it **must not**
    /// be "forgotten" (e.g. `core::mem::forget`), or being targeted of any
    /// other operation that would prevent it from executing its `drop` call.
    unsafe fn lock_with<'a>(&'a self, node: &'a MutexNode) -> MutexGuard<'a, T, R> {
        debug_assert_node!(node);
        let pred = self.tail.swap(node.as_ptr(), AcqRel);
        // If we have a predecessor, than we need to wait for the hand-off.
        if !pred.is_null() {
            // Wait for predecessor to transfer lock ownership to this thread,
            // while applying some relax strategy.
            // SAFETY: Already verified that our predecessor is not null.
            unsafe { &*pred }.wait_transfer_release(self.as_ptr());
            fence(Acquire);
        }
        MutexGuard::new(self, node)
    }

    /// Unlocks this mutex. If there is a successor node in the queue, the lock
    /// is passed directly to them.
    fn unlock_with(&self, head: &MutexNode) {
        debug_assert_node!(head);
        // If were are not the tail, then we have a successor.
        if !self.try_unlock_release(head.as_ptr()) {
            // Signal to the successor that this lock is ready to be transfered.
            head.grant.store(self.as_addr(), Release);
            // Wait for successor to acknowledge the lock ownership transfer,
            // while applying some relax strategy.
            head.wait_acknowledgment_relaxed::<R>();
            fence(Acquire);
        }
    }
}

impl<T: ?Sized, R> Mutex<T, R> {
    #[inline]
    pub fn is_locked(&self) -> bool {
        !self.tail.load(Relaxed).is_null()
    }

    #[cfg(not(all(loom, test)))]
    #[inline(always)]
    pub fn get_mut(&mut self) -> &mut T {
        // SAFETY: We hold exclusive access to the Mutex data.
        unsafe { &mut *self.data.get() }
    }

    /// Returns a raw immutable pointer of this lock.
    const fn as_ptr(&self) -> *const Self {
        self as *const Self
    }

    /// Returns the "address" portion of the reference.
    fn as_addr(&self) -> usize {
        self.as_ptr().cast::<()>() as usize
    }

    /// Returns the "address" portion of the pointer.
    fn addr(this: *const Self) -> usize {
        this.cast::<()>() as usize
    }

    /// Unlocks the lock if the candidate node is the queue's tail.
    fn try_unlock_release(&self, node: *mut MutexNode) -> bool {
        self.tail.compare_exchange(node, ptr::null_mut(), Release, Relaxed).is_ok()
    }
}

impl<T: Default, R> Default for Mutex<T, R> {
    /// Creates a `Mutex<T, R>`, with the `Default` value for `T`.
    #[inline]
    fn default() -> Self {
        Self::new(Default::default())
    }
}

impl<T, R> From<T> for Mutex<T, R> {
    /// Creates a `Mutex<T, R>` from a instance of `T`.
    #[inline]
    fn from(data: T) -> Self {
        Self::new(data)
    }
}

impl<T: ?Sized + Debug, R: Relax> Debug for Mutex<T, R> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("Mutex");
        self.try_lock_then(|data| match data {
            Some(data) => d.field("data", &data),
            None => d.field("data", &format_args!("<locked>")),
        });
        d.finish()
    }
}

#[cfg(test)]
impl<T: ?Sized, R> LockNew for Mutex<T, R> {
    type Target = T;

    fn new(value: Self::Target) -> Self
    where
        Self::Target: Sized,
    {
        Self::new(value)
    }
}

#[cfg(test)]
impl<T: ?Sized, R: Relax> LockWithThen for Mutex<T, R> {
    type Node = MutexNode;

    type Guard<'a>
        = &'a mut Self::Target
    where
        Self: 'a,
        Self::Target: 'a;

    fn lock_with_then<F, Ret>(&self, node: &mut Self::Node, f: F) -> Ret
    where
        F: FnOnce(&mut Self::Target) -> Ret,
    {
        self.lock_with_then(node, f)
    }
}

#[cfg(test)]
impl<T: ?Sized, R: Relax> TryLockWithThen for Mutex<T, R> {
    fn try_lock_with_then<F, Ret>(&self, node: &mut Self::Node, f: F) -> Ret
    where
        F: FnOnce(Option<&mut Self::Target>) -> Ret,
    {
        self.try_lock_with_then(node, f)
    }

    fn is_locked(&self) -> bool {
        self.is_locked()
    }
}

#[cfg(test)]
impl<T: ?Sized, R: Relax> LockThen for Mutex<T, R> {
    fn lock_then<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(&mut Self::Target) -> Ret,
    {
        self.lock_then(f)
    }
}

#[cfg(test)]
impl<T: ?Sized, R: Relax> TryLockThen for Mutex<T, R> {
    fn try_lock_then<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<&mut Self::Target>) -> Ret,
    {
        self.try_lock_then(f)
    }
}

#[cfg(all(not(loom), test))]
impl<T: ?Sized, R> crate::test::LockData for Mutex<T, R> {
    fn into_inner(self) -> Self::Target
    where
        Self::Target: Sized,
    {
        self.into_inner()
    }

    fn get_mut(&mut self) -> &mut Self::Target {
        self.get_mut()
    }
}

#[must_use = "if unused the Mutex will immediately unlock"]
struct MutexGuard<'a, T: ?Sized, R: Relax> {
    lock: &'a Mutex<T, R>,
    head: &'a MutexNode,
}

// Same unsafe Sync impl as `std::sync::MutexGuard`.
unsafe impl<T: ?Sized + Sync, R: Relax> Sync for MutexGuard<'_, T, R> {}

impl<'a, T: ?Sized, R: Relax> MutexGuard<'a, T, R> {
    /// Creates a new `MutexGuard` instance.
    const fn new(lock: &'a Mutex<T, R>, head: &'a MutexNode) -> Self {
        Self { lock, head }
    }

    /// Runs `f` against a shared reference pointing to the underlying data.
    #[cfg(not(tarpaulin_include))]
    fn with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(&T) -> Ret,
    {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { self.lock.data.with_unchecked(f) }
    }

    /// Runs `f` against a mutable reference pointing to the underlying data.
    fn with_mut<F, Ret>(&mut self, f: F) -> Ret
    where
        F: FnOnce(&mut T) -> Ret,
    {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { self.lock.data.with_mut_unchecked(f) }
    }
}

/// A trait that converts a `&mut Self` to a `Option<&mut Self::Target>` and
/// then runs closures against it.
pub trait AsDerefMutWithMut {
    type Target: ?Sized;

    /// Converts `&mut Self` to `Option<&mut Self::Target>` and then runs `f`
    /// against it.
    fn as_deref_mut_with_mut<F, Ret>(&mut self, f: F) -> Ret
    where
        F: FnOnce(Option<&mut Self::Target>) -> Ret;
}

impl<T: ?Sized, R: Relax> AsDerefMutWithMut for Option<MutexGuard<'_, T, R>> {
    type Target = T;

    fn as_deref_mut_with_mut<F, Ret>(&mut self, f: F) -> Ret
    where
        F: FnOnce(Option<&mut Self::Target>) -> Ret,
    {
        let data = self.as_ref().map(|guard| &guard.lock.data);
        // SAFETY: A guard instance holds the lock locked.
        unsafe { data.as_deref_with_mut_unchecked(f) }
    }
}

#[cfg(not(tarpaulin_include))]
impl<T: ?Sized + Debug, R: Relax> Debug for MutexGuard<'_, T, R> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.with(|data| data.fmt(f))
    }
}

#[cfg(not(tarpaulin_include))]
impl<T: ?Sized + Display, R: Relax> Display for MutexGuard<'_, T, R> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.with(|data| data.fmt(f))
    }
}

#[cfg(not(all(loom, test)))]
#[cfg(not(tarpaulin_include))]
impl<T: ?Sized, R: Relax> core::ops::Deref for MutexGuard<'_, T, R> {
    type Target = T;

    /// Dereferences the guard to access the underlying data.
    #[inline(always)]
    fn deref(&self) -> &T {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { &*self.lock.data.get() }
    }
}

#[cfg(not(all(loom, test)))]
#[cfg(not(tarpaulin_include))]
impl<T: ?Sized, R: Relax> core::ops::DerefMut for MutexGuard<'_, T, R> {
    /// Mutably dereferences the guard to access the underlying data.
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { &mut *self.lock.data.get() }
    }
}

impl<T: ?Sized, R: Relax> Drop for MutexGuard<'_, T, R> {
    #[inline]
    fn drop(&mut self) {
        self.lock.unlock_with(self.head);
    }
}

#[cfg(all(not(loom), test))]
mod test {
    use crate::raw::yields::Mutex;
    use crate::test::tests;

    #[test]
    fn lots_and_lots_lock() {
        tests::lots_and_lots_lock::<Mutex<_>>();
    }

    #[test]
    fn lots_and_lots_try_lock() {
        tests::lots_and_lots_try_lock::<Mutex<_>>();
    }

    #[test]
    fn lots_and_lots_mixed_lock() {
        tests::lots_and_lots_mixed_lock::<Mutex<_>>();
    }

    #[test]
    fn smoke() {
        tests::smoke::<Mutex<_>>();
    }

    #[test]
    fn test_mutex_debug() {
        tests::test_mutex_debug::<Mutex<_>>();
    }

    #[test]
    fn test_mutex_from() {
        tests::test_mutex_from::<Mutex<_>>();
    }

    #[test]
    fn test_mutex_default() {
        tests::test_mutex_default::<Mutex<_>>();
    }

    #[test]
    fn test_try_lock() {
        tests::test_try_lock::<Mutex<_>>();
    }

    #[test]
    fn test_into_inner() {
        tests::test_into_inner::<Mutex<_>>();
    }

    #[test]
    fn test_into_inner_drop() {
        tests::test_into_inner_drop::<Mutex<_>>();
    }

    #[test]
    fn test_get_mut() {
        tests::test_get_mut::<Mutex<_>>();
    }

    #[test]
    fn test_lock_arc_nested() {
        tests::test_lock_arc_nested::<Mutex<_>, Mutex<_>>();
    }

    #[test]
    fn test_acquire_more_than_one_lock() {
        tests::test_acquire_more_than_one_lock::<Mutex<_>>();
    }

    #[test]
    fn test_lock_arc_access_in_unwind() {
        tests::test_lock_arc_access_in_unwind::<Mutex<_>>();
    }

    #[test]
    fn test_lock_unsized() {
        tests::test_lock_unsized::<Mutex<_>>();
    }
}

#[cfg(all(loom, test))]
mod model {
    use crate::loom::models;
    use crate::raw::yields::Mutex;

    #[test]
    fn try_lock_join() {
        models::try_lock_join::<Mutex<_>>();
    }

    #[test]
    fn lock_join() {
        models::lock_join::<Mutex<_>>();
    }

    #[test]
    fn mixed_lock_join() {
        models::mixed_lock_join::<Mutex<_>>();
    }
}
