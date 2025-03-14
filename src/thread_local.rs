/// Non-recursive, inner definition of `thread_local_node!`.
///
/// This macro is **NOT** part of the public API and so must not be called
/// directly by user's code. It is subjected to changes **WITHOUT** prior
/// notice or accompanied with relevant SemVer changes.
#[cfg(not(all(loom, test)))]
#[doc(hidden)]
#[macro_export]
macro_rules! __thread_local_node_inner {
    ($vis:vis $node:ident, $($mod:ident)::+) => {
        $vis const $node: $crate::$($mod::)+LocalMutexNode = {
            ::std::thread_local! {
                static NODE: $crate::$($mod::)+MutexNode = const {
                    $crate::$($mod::)+MutexNode::new()
                };
            }
            $crate::$($mod::)+LocalMutexNode::__new(NODE)
        };
    };
}

/// Non-recursive, Loom based inner definition of `thread_local_node!`.
///
/// This node definition uses Loom primitives and it can't be evaluated at
/// compile-time since Loom does not support that feature. Loom's `thread_local!`
/// macro defines a `static` value as oppose to std's `const` value.
#[cfg(all(loom, test))]
#[macro_export]
macro_rules! __thread_local_node_inner {
    ($vis:vis $node:ident, $($mod:ident)::+) => {
        $vis static $node: $crate::$($mod::)+LocalMutexNode = {
            ::loom::thread_local! {
                static NODE: $crate::$($mod::)+MutexNode = {
                    $crate::$($mod::)+MutexNode::new()
                };
            }
            $crate::$($mod::)+LocalMutexNode::new(&NODE)
        };
    };
}
