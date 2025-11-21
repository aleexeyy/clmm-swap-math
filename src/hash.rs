#[cfg(all(
    feature = "rustc-hash",
    not(any(feature = "ahash", feature = "std-hash"))
))]
pub type FastMap<K, V> = rustc_hash::FxHashMap<K, V>;

#[cfg(all(
    feature = "ahash",
    not(any(feature = "rustc-hash", feature = "std-hash"))
))]
pub type FastMap<K, V> = ahash::AHashMap<K, V>;

#[cfg(any(
    all(
        not(feature = "rustc-hash"),
        not(feature = "ahash"),
        not(feature = "std-hash")
    ),
    feature = "std-hash",
    all(feature = "rustc-hash", feature = "ahash"),
    all(feature = "rustc-hash", feature = "std-hash"),
    all(feature = "ahash", feature = "std-hash"),
))]
pub type FastMap<K, V> = std::collections::HashMap<K, V>;
