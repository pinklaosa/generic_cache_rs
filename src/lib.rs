//! A generic cached object which provide user two possible usage options.
//! 1. Use [Object::get()] until it return [TimeoutError] then manually call [Object::refresh()] function.
//! 1. Use [Object::get_or_refresh()] which will automatically refresh the value when it is expired.
//!
//! The different between the two is that the [Object::get()] is more flexible because it only borrow
//! the cache value while the [Object::get_or_refresh()] will required a borrow mut of [Object] itself because it
//! might need to change the cached value. However, the auto refresh is convenient because user doesn't
//! need to handle [TimeoutError] when cache is expired.
//! Both usage options still need to handle `refresh_fn` error if any.
//!
//! # Example
//! - Verify two cached call to get value back to back to check if it is actually the same value.
//! ```rust
//! use generic_cache::{CachedObject, Object};
//!
//! let cached = Object::new(std::time::Duration::from_secs(1), 100, async || {Ok::<u16, ()>(200)}); // Explicitly define type for Error. Otherwise, compile will fail.
//! let first = cached.get().unwrap();
//! let second = cached.get().unwrap();
//! assert_eq!(*first, 100, "Expect {} to equals {}", *first, 0);
//! assert_eq!(first, second, "Expect {} to equals {}", first, second);
//! ```
//! - Check for expired then refresh the cache
//! ```rust
//! use core::time;
//! use std::thread::sleep;
//! use generic_cache::Object;
//!
//! # tokio_test::block_on(async {
//! let mut cached = Object::new(std::time::Duration::from_millis(100), 100, async || {Ok::<u16, ()>(200)}); // Explicitly define type for Error. Otherwise, compile will fail.
//! let first = *cached.get().unwrap();
//! sleep(time::Duration::from_millis(200));
//! if let Ok(_) = cached.get() {
//!     panic!("Cache should be expired but it is not.")
//! } else {
//!     cached.refresh().await.unwrap();
//! }
//! let second = *cached.get().unwrap();
//! assert_ne!(first, second, "Expect {} to equals {}", first, second);
//! # })
//! ```
//! - Auto refresh expired cache value
//! ```rust
//! use core::time;
//! use std::thread::sleep;
//! use generic_cache::Object;
//!
//! # tokio_test::block_on(async {
//! let mut cached = Object::new(std::time::Duration::from_secs(0), 100, async || {Ok::<u16, ()>(200)}); // Explicitly define type for Error. Otherwise, compile will fail.
//! let first = *cached.get_or_refresh().await.unwrap();
//! sleep(time::Duration::from_millis(1));
//! let second = *cached.get_or_refresh().await.unwrap();
//! assert_eq!(first, second, "Expect {} to equals {}", first, second);
//! # })
//! ```
//! - No default value when create a cache and auto refresh expired cache value
//! ```rust
//! use core::time;
//! use std::thread::sleep;
//! use generic_cache::Object;
//!
//! # tokio_test::block_on(async {
//! let mut cached = Object::new_and_refresh(std::time::Duration::from_secs(1), async || {Ok::<u16, ()>(200)}).await.unwrap(); // Explicitly define type for Error. Otherwise, compile will fail.
//! let first = *cached.get_or_refresh().await.unwrap();
//! let second = *cached.get_or_refresh().await.unwrap();
//! assert_eq!(first, second, "Expect {} to equals {}", first, second);
//! # })
//! ```
use std::fmt::{Debug, Display, Formatter};
use std::future::Future;
use std::pin::Pin;
use std::time::{Duration, SystemTime};
/// The cache is timeout. [Object::refresh()] need to be called.
#[derive(Clone, Copy)]
pub struct TimeoutError;
impl std::error::Error for TimeoutError {}
impl Display for TimeoutError {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(
            fmt,
            "The cached object is timeout. Please call refresh method to refresh the value."
        )
    }
}
impl Debug for TimeoutError {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(
            fmt,
            "The cached object is timeout. Please call refresh method to refresh the value."
        )
    }
}

/// Generic cache object which cache an object for given period of time before it return TimeoutError
/// to signal caller to call refresh function before further attempt.
/// The refresh_fn should be async function that return Result of the same type as the cached object.
/// If there's any error occur inside refresh_fn, it should return Error result back.
#[derive(Clone, Copy)]
pub struct Object<T, F, E = ()>
where
    F: AsyncFnMut() -> Result<T, E>,
{
    ttl: Duration,
    last_update: SystemTime,
    obj: T,
    refresh_fn: F,
}
impl<T, F, E> Debug for Object<T, F, E>
where
    T: Debug,
    F: AsyncFnMut() -> Result<T, E>,
{
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(
            fmt,
            "{{ttl: {} us, elapsed: {}, obj: {:#?}}}",
            self.ttl.as_micros(),
            self.last_update.elapsed().unwrap().as_millis(),
            self.obj
        )
    }
}
/// A trait to provide a type that hides async refresh function.
/// It allows user to use `dyn CachedObject` as a trait object or
/// use `impl CachedObject` to allow compile time trait realization.
///
/// Note that this trait return `Pin<Box<dyn Future>>` instead of `impl Future` because
/// it allows `dyn CachedObject` to be used in a trait object context.
///
/// This will incur some performance overhead because it requires heap allocation.
///
/// This behavior is different from [Object] which return `impl Future` that may not
/// allocate on heap.
///
/// Usage example, static interior mutability with [std::sync::LazyLock] and [std::sync::RwLock] to create a global thread safe cached object.
/// ```rust
/// # tokio_test::block_on(async {
/// use core::time::Duration;
/// use generic_cache::{CachedObject, Object};
/// use std::sync::{LazyLock, RwLock};
/// use tokio::time::sleep;
///
/// static CACHED: LazyLock<RwLock<Box<dyn CachedObject<u16, ()> + Send + Sync>>> = LazyLock::new(|| {
///    RwLock::new(Box::new(Object::new(std::time::Duration::from_secs(1), 100, async || {Ok::<u16, ()>(200)})))
/// });
/// assert_eq!((&*CACHED).read().unwrap().get().unwrap(), &100u16);
/// sleep(Duration::from_secs(2)).await;
/// assert!((&*CACHED).read().unwrap().get().is_err(), "Cache should be expired");
/// assert_eq!((&*CACHED).write().unwrap().get_or_refresh().await.unwrap(), &200u16, "Cache should be refreshed to 200");
/// # })
/// ```
/// Until https://github.com/rust-lang/rust/issues/63065 is resolved,
/// we cannot use `impl CachedObject` in a static binding so `dyn CachedObject` is currently the
/// only solution available.
pub trait CachedObject<T, E> {
    /// Refresh cache immediately and update last update time if refresh success.
    fn refresh(&mut self) -> Pin<Box<dyn Future<Output = Result<(), E>> + '_>>;
    /// Read current cached value or return Error if cache is already expired.
    fn get(&self) -> Result<&T, TimeoutError>;
    /// Read current cached value or refresh the value if it is already expired then
    /// return the new value.
    fn get_or_refresh<'a>(&'a mut self) -> Pin<Box<dyn Future<Output = Result<&'a T, E>> + 'a>>
    where
        T: 'a;
    /// Get time remain that the cache still valid.
    /// In other word, time remain before it return [TimeoutError] on [Object::get] function.
    fn time_remain(&self) -> Duration;
}

impl<T, F, E> CachedObject<T, E> for Object<T, F, E>
where
    F: AsyncFnMut() -> Result<T, E>,
{
    #[inline(always)]
    fn refresh(&mut self) -> Pin<Box<dyn Future<Output = Result<(), E>> + '_>> {
        Box::pin(Object::refresh(self))
    }
    #[inline(always)]
    fn get(&self) -> Result<&T, TimeoutError> {
        Object::get(&self)
    }
    #[inline(always)]
    fn get_or_refresh<'a>(&'a mut self) -> Pin<Box<dyn Future<Output = Result<&'a T, E>> + 'a>>
    where
        T: 'a,
    {
        Box::pin(Object::get_or_refresh(self))
    }
    #[inline(always)]
    fn time_remain(&self) -> Duration {
        Object::time_remain(&self)
    }
}
impl<T, F, E> Object<T, F, E>
where
    F: AsyncFnMut() -> Result<T, E>,
{
    /// Create a new cached Object with default value specify in second argument.
    /// `ttl` is "time to live" which is duration that the cached value will be return.
    /// `refresh_fn` is a function to refresh value and last update time.
    pub fn new(ttl: Duration, obj: T, refresh_fn: F) -> Object<T, F, E> {
        Object {
            ttl,
            last_update: SystemTime::now(),
            obj,
            refresh_fn,
        }
    }
    /// Create a new cached Object and immediately refresh the value instead of using default value.
    /// `ttl` is "time to live" which is duration that the cached value will be return.
    /// `refresh_fn` is a function to refresh value and last update time.
    /// The different from `new` function is that it is async and it immediately call `refresh_fn`.
    pub async fn new_and_refresh(ttl: Duration, mut refresh_fn: F) -> Result<Object<T, F, E>, E> {
        let v = refresh_fn().await?;
        let obj = Object {
            ttl,
            last_update: SystemTime::now(),
            obj: v,
            refresh_fn,
        };
        Ok(obj)
    }
    /// Refresh cache immediately and update last update time if refresh success.
    pub async fn refresh(&mut self) -> Result<(), E> {
        self.obj = (self.refresh_fn)().await?;
        self.last_update = SystemTime::now();
        Ok(())
    }
    /// Read current cached value or return Error if cache is already expired.
    pub fn get(&self) -> Result<&T, TimeoutError> {
        if self.last_update.elapsed().unwrap() > self.ttl {
            return Err(TimeoutError {});
        }
        Ok(&self.obj)
    }
    /// Read current cached value or refresh the value if it is already expired then
    /// return the new value.
    pub async fn get_or_refresh(&mut self) -> Result<&T, E> {
        if self.last_update.elapsed().unwrap() >= self.ttl {
            self.obj = (self.refresh_fn)().await?;
        }
        Ok(&self.obj)
    }
    /// Get time remain that the cache still valid.
    /// In other word, time remain before it return [TimeoutError] on [Object::get] function.
    pub fn time_remain(&self) -> Duration {
        let elapsed = self.last_update.elapsed().unwrap();
        if elapsed > self.ttl {
            Duration::from_micros(0u64)
        } else {
            self.ttl - elapsed
        }
    }
}
#[cfg(test)]
mod tests {
    use core::time;
    use std::{thread::sleep, time::Duration};

    use super::*;

    #[test]
    fn simple_cache() {
        let cached = Object::new(Duration::from_secs(1), 100, async || Ok::<u16, ()>(200));
        let first = cached.get().unwrap();
        let second = cached.get().unwrap();
        assert_eq!(*first, 100, "Expect {} to equals {}", *first, 0);
        assert_eq!(first, second, "Expect {} to equals {}", first, second);
    }
    #[tokio::test]
    async fn simple_refresh() {
        let mut cached = Object::new(Duration::from_secs(1), 100, async || Ok::<u16, ()>(200));
        let first = *cached.get().unwrap();
        cached.refresh().await.unwrap();
        let second = *cached.get().unwrap();
        assert_eq!(first, 100, "Expect {} to equals {}", first, 100);
        assert_eq!(second, 200, "Expect {} to equals {}", first, 200);
    }
    #[tokio::test]
    async fn simple_no_cache() {
        let mut cached = Object::new(Duration::ZERO, 100, async || Ok::<u16, ()>(200));
        let first = *cached.get_or_refresh().await.unwrap();
        sleep(time::Duration::from_millis(1));
        let second = *cached.get_or_refresh().await.unwrap();
        assert_eq!(first, 200, "Expect {} to equals {}", first, 200);
        assert_eq!(first, second, "Expect {} to equals {}", first, second);
    }
    #[tokio::test]
    async fn simple_expire_check() {
        let mut cached = Object::new(Duration::from_millis(1), 100, async || Ok::<u16, ()>(200));
        let first = *cached.get().unwrap();
        sleep(time::Duration::from_millis(1));
        if let Ok(_) = cached.get() {
            panic!("Cache should be expired but it is not.")
        } else {
            cached.refresh().await.unwrap();
        }
        let second = *cached.get().unwrap();
        assert_ne!(first, second, "Expect {} to equals {}", first, second);
    }
    #[tokio::test]
    async fn immediate_refresh() {
        let mut cached =
            Object::new_and_refresh(Duration::from_secs(1), async || Ok::<u16, ()>(200))
                .await
                .unwrap();
        let first = *cached.get_or_refresh().await.unwrap();
        let second = *cached.get_or_refresh().await.unwrap();
        assert_eq!(first, second, "Expect {} to equals {}", first, second);
    }
    #[tokio::test]
    async fn time_remain_validate() {
        let mut cached = Object::new(Duration::from_secs(5), 100, async || Ok::<u16, ()>(200));
        sleep(Duration::from_secs(1));
        let original_remain = cached.time_remain();
        println!("Original time remain is {:?}", original_remain);
        cached.refresh().await.unwrap();
        let new_remain = cached.time_remain();
        println!("New time remain is {:?}", new_remain);
        assert!(
            new_remain > original_remain,
            "Original time remain should be less than a fresh new value time remain."
        );
    }
    #[test]
    fn simple_object() {
        struct Dummy {
            v: u8,
        }
        let cached = Object::new(Duration::from_secs(1), Dummy { v: 1 }, async || {
            Ok::<Dummy, ()>(Dummy { v: 2 })
        });
        let Dummy { v: v1 } = cached.get().unwrap();
        let Dummy { v: v2 } = cached.get().unwrap();
        assert_eq!(*v1, 1, "Expect {} to equals {}", v1, 1);
        assert_eq!(v1, v2, "Expect {} to equals {}", v1, v2);
    }
    #[tokio::test]
    async fn simple_object_mut() {
        let mut count = 0u8;
        struct Dummy {
            v: u8,
        }
        let mut cached = Object::new(Duration::from_secs(1), Dummy { v: 1 }, async || {
            count += 1;
            Ok::<Dummy, ()>(Dummy { v: 2 })
        });
        let Dummy { v: v1 } = cached.get().unwrap();
        let Dummy { v: v2 } = cached.get().unwrap();
        let original = *v1;
        assert_eq!(*v1, 1, "Expect {} to equals {}", v1, 1);
        assert_eq!(*v1, *v2, "Expect {} to equals {}", v1, v2);
        cached.refresh().await.expect("to get a new value");
        let Dummy { v: new_v } = cached.get().unwrap();
        assert_ne!(original, *new_v, "Expect to get a new value");
        assert_eq!(count, 1, "counter should be 1");
    }
}
