//! Round-trip proof obligations for the codec traits.
//!
//! `cfg(hax)`-only; compiled out of every ordinary build.

use alloc::string::String;
use alloc::vec::Vec;

use crate::{
    DeserializeBytes, Error, SerializeBytes, TlsByteVecU8, TlsByteVecU16, TlsByteVecU24,
    TlsByteVecU32, TlsVarInt, U24, VLBytes,
};

macro_rules! round_trip {
    ($encode_decode:ident, $decode_encode:ident, $t:ty) => {
        /// Serialize, then deserialize: the identity on values.
        #[hax_lib::ensures(|res| res.is_err()
            || res.is_ok_and(|(out, remaining)| out == *value && remaining == 0))]
        pub fn $encode_decode(value: &$t) -> Result<($t, usize), Error> {
            let bytes = value.tls_serialize_bytes()?;
            let (out, remainder) = <$t>::tls_deserialize_bytes(&bytes)?;
            Ok((out, remainder.len()))
        }

        round_trip!(@decode_encode $decode_encode, $t);
    };
    ($encode_decode:ident, $decode_encode:ident, $t:ty, requires |$value:ident| $pre:expr) => {
        /// Serialize, then deserialize: the identity on values.
        #[hax_lib::requires($pre)]
        #[hax_lib::ensures(|res| res.is_err()
            || res.is_ok_and(|(out, remaining)| out == *$value && remaining == 0))]
        pub fn $encode_decode($value: &$t) -> Result<($t, usize), Error> {
            let bytes = $value.tls_serialize_bytes()?;
            let (out, remainder) = <$t>::tls_deserialize_bytes(&bytes)?;
            Ok((out, remainder.len()))
        }

        round_trip!(@decode_encode $decode_encode, $t);
    };
    (@decode_encode $decode_encode:ident, $t:ty) => {
        /// Deserialize, then serialize: the identity on the bytes consumed.
        #[hax_lib::ensures(|res| res.is_err()
            || res.is_ok_and(|(out, consumed)| bytes.get(..consumed) == Some(out.as_slice())))]
        pub fn $decode_encode(bytes: &[u8]) -> Result<(Vec<u8>, usize), Error> {
            let (value, remainder) = <$t>::tls_deserialize_bytes(bytes)?;
            let consumed = bytes.len() - remainder.len();
            let out = value.tls_serialize_bytes()?;
            Ok((out, consumed))
        }
    };
}

round_trip!(u8_encode_decode, u8_decode_encode, u8);
round_trip!(u16_encode_decode, u16_decode_encode, u16);
round_trip!(u32_encode_decode, u32_decode_encode, u32);
round_trip!(u64_encode_decode, u64_decode_encode, u64);
round_trip!(u24_encode_decode, u24_decode_encode, U24);
round_trip!(array4_encode_decode, array4_decode_encode, [u8; 4]);
round_trip!(option_u16_encode_decode, option_u16_decode_encode, Option<u16>);

round_trip!(varint_encode_decode, varint_decode_encode, TlsVarInt,
    requires |value| value.value() <= TlsVarInt::MAX);

round_trip!(vlbytes_encode_decode, vlbytes_decode_encode, VLBytes);

round_trip!(byte_vec_u8_encode_decode, byte_vec_u8_decode_encode, TlsByteVecU8);
round_trip!(byte_vec_u16_encode_decode, byte_vec_u16_decode_encode, TlsByteVecU16);
round_trip!(byte_vec_u24_encode_decode, byte_vec_u24_decode_encode, TlsByteVecU24);
round_trip!(byte_vec_u32_encode_decode, byte_vec_u32_decode_encode, TlsByteVecU32);

round_trip!(vec_u16_encode_decode, vec_u16_decode_encode, Vec<u16>);

round_trip!(string_encode_decode, string_decode_encode, String);
