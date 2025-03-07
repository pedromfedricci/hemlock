mod mutex;
pub use mutex::{Mutex, MutexNode};

#[cfg(feature = "thread_local")]
#[cfg_attr(docsrs, doc(cfg(feature = "thread_local")))]
mod thread_local;
#[cfg(feature = "thread_local")]
pub use thread_local::LocalMutexNode;

pub mod spins {
    use super::mutex;
    use crate::relax::Spin;

    pub type Mutex<T> = mutex::Mutex<T, Spin>;

    pub mod backoff {
        use super::mutex;
        use crate::relax::SpinBackoff;

        pub type Mutex<T> = mutex::Mutex<T, SpinBackoff>;
    }
}

#[cfg(any(feature = "yield", loom, test))]
#[cfg_attr(docsrs, doc(cfg(feature = "yield")))]
pub mod yields {
    use super::mutex;
    use crate::relax::Yield;

    pub type Mutex<T> = mutex::Mutex<T, Yield>;

    pub mod backoff {
        use super::mutex;
        use crate::relax::YieldBackoff;

        pub type Mutex<T> = mutex::Mutex<T, YieldBackoff>;
    }
}

pub mod loops {
    use super::mutex;
    use crate::relax::Loop;

    pub type Mutex<T> = mutex::Mutex<T, Loop>;
}
