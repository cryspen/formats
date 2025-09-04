use super::{
    Deserialize, Error, Serialize, tls_deserialize_exact_default, tls_serialize_detached_default,
};
use alloc::vec::Vec;

// This module contains the workaround for https://github.com/cryspen/hax/issues/888

pub trait SerializeDetached {
    /// Serialize `self` and return it as a byte vector.
    #[cfg(feature = "std")]
    fn tls_serialize_detached(&self) -> Result<Vec<u8>, Error>;
}

impl<T: Serialize> SerializeDetached for T {
    /// Serialize `self` and return it as a byte vector.
    #[cfg(feature = "std")]
    fn tls_serialize_detached(&self) -> Result<Vec<u8>, Error> {
        tls_serialize_detached_default(self)
    }
}

pub trait DeserializeExact: Deserialize {
    /// This function deserializes the provided `bytes` and returns the populated
    /// struct. All bytes must be consumed.
    ///
    /// Returns an error if not all bytes are read from the input, or if an error
    /// occurs during deserialization.
    #[cfg(feature = "std")]
    fn tls_deserialize_exact(bytes: impl AsRef<[u8]>) -> Result<Self, Error>
    where
        Self: Sized;
}

impl<T: Deserialize> DeserializeExact for T {
    /// This function deserializes the provided `bytes` and returns the populated
    /// struct. All bytes must be consumed.
    ///
    /// Returns an error if not all bytes are read from the input, or if an error
    /// occurs during deserialization.
    #[cfg(feature = "std")]
    fn tls_deserialize_exact(bytes: impl AsRef<[u8]>) -> Result<Self, Error>
    where
        Self: Sized,
    {
        tls_deserialize_exact_default(bytes)
    }
}
