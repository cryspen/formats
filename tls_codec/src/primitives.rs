//! Codec implementations for unsigned integer primitives.

use alloc::{boxed::Box, vec::Vec};

use crate::{DeserializeBytes, SerializeBytes, SizeChecked, U24};

use super::{Deserialize, Error, Serialize, Size};

#[cfg(hax)]
use hax_lib::ToInt;

use core::marker::PhantomData;
#[cfg(feature = "std")]
use std::io::{Read, Write};

macro_rules! add {
    ($x: expr, $y: expr) => {
        if cfg!(debug_assertions) {
            $x.checked_add($y).ok_or(Error::LibraryError)?
        } else {
            $x + $y
        }
    };
}
pub(crate) use add;

impl<T: Size> Size for Option<T> {
    #[inline]
    fn tls_serialized_len(&self) -> usize {
        1 + match self {
            Some(v) => {
                hax_lib::assume!(v.tls_serialized_len() < usize::MAX);
                v.tls_serialized_len()
            }
            None => 0,
        }
    }
}

impl<T: SizeChecked> SizeChecked for Option<T> {
    #[inline]
    fn tls_serialized_len_checked(&self) -> Option<usize> {
        1usize.checked_add(match self {
            Some(v) => v.tls_serialized_len_checked()?,
            None => 0,
        })
    }
}

impl<T: Size> Size for &Option<T> {
    #[inline]
    fn tls_serialized_len(&self) -> usize {
        (*self).tls_serialized_len()
    }
}

impl<T: SizeChecked> SizeChecked for &Option<T> {
    #[inline]
    fn tls_serialized_len_checked(&self) -> Option<usize> {
        (*self).tls_serialized_len_checked()
    }
}

impl<T: Serialize> Serialize for Option<T> {
    #[cfg(feature = "std")]
    fn tls_serialize<W: Write>(&self, writer: &mut W) -> Result<usize, Error> {
        match self {
            Some(e) => {
                let written = writer.write(&[1])?;
                hax_lib::assume!(written == 1);
                debug_assert_eq!(written, 1);
                Ok(add!(e.tls_serialize(writer)?, 1))
            }
            None => {
                writer.write_all(&[0])?;
                Ok(1)
            }
        }
    }
}

impl<T: SerializeBytes> SerializeBytes for Option<T> {
    #[inline]
    fn tls_serialize(&self) -> Result<Vec<u8>, Error> {
        match self {
            Some(e) => {
                let mut out = Vec::with_capacity(add!(e.tls_serialized_len(), 1));
                out.push(1);
                // Not inlining serialized_e is a workaround for
                // https://github.com/cryspen/hax/issues/1584
                let mut serialized_e = e.tls_serialize()?;
                // Could be turned into a post-condition on `tls_serialize`
                hax_lib::assume!(serialized_e.len() == e.tls_serialized_len());
                out.append(&mut serialized_e);
                Ok(out)
            }
            None => Ok(vec![0]),
        }
    }
}

impl<T: Serialize> Serialize for &Option<T> {
    #[cfg(feature = "std")]
    fn tls_serialize<W: Write>(&self, writer: &mut W) -> Result<usize, Error> {
        (*self).tls_serialize(writer)
    }
}

impl<T: SerializeBytes> SerializeBytes for &Option<T> {
    #[inline]
    fn tls_serialize(&self) -> Result<Vec<u8>, Error> {
        (*self).tls_serialize()
    }
}

impl<T: Deserialize> Deserialize for Option<T> {
    #[cfg(feature = "std")]
    #[inline]
    fn tls_deserialize<R: Read>(bytes: &mut R) -> Result<Self, Error> {
        let mut some_or_none = [0u8; 1];
        bytes.read_exact(&mut some_or_none)?;
        match some_or_none[0] {
            0 => Ok(None),
            1 => {
                let element = T::tls_deserialize(bytes)?;
                Ok(Some(element))
            }
            _ => Err(Error::DecodingError(format!(
                "Trying to decode Option<T> with {} for option. It must be 0 for None and 1 for Some.",
                some_or_none[0]
            ))),
        }
    }
}

impl<T: DeserializeBytes> DeserializeBytes for Option<T> {
    #[inline]
    fn tls_deserialize_bytes(bytes: &[u8]) -> Result<(Self, &[u8]), Error> {
        let (some_or_none, remainder) = <u8>::tls_deserialize_bytes(bytes)?;
        match some_or_none {
            0 => Ok((None, remainder)),
            1 => {
                let (element, remainder) = T::tls_deserialize_bytes(remainder)?;
                Ok((Some(element), remainder))
            }
            _ => Err(Error::DecodingError(alloc::format!(
                "Trying to decode Option<T> with {some_or_none} for option. It must be 0 for None and 1 for Some."
            ))),
        }
    }
}

macro_rules! impl_unsigned {
    ($t:ty, $bytes:literal) => {
        impl Deserialize for $t {
            #[cfg(feature = "std")]
            #[inline]
            fn tls_deserialize<R: Read>(bytes: &mut R) -> Result<Self, Error> {
                let mut x = <$t>::default().to_be_bytes();
                bytes.read_exact(&mut x)?;
                Ok(<$t>::from_be_bytes(x))
            }
        }

        impl DeserializeBytes for $t {
            #[inline]
            fn tls_deserialize_bytes(bytes: &[u8]) -> Result<(Self, &[u8]), Error> {
                let len = core::mem::size_of::<$t>();
                let out = bytes
                    .get(..len)
                    .ok_or(Error::EndOfStream)?
                    .try_into()
                    .map_err(|_| Error::EndOfStream)?;
                Ok((
                    <$t>::from_be_bytes(out),
                    &bytes.get(len..).ok_or(Error::EndOfStream)?,
                ))
            }
        }

        impl SerializeBytes for &$t {
            #[inline]
            fn tls_serialize(&self) -> Result<Vec<u8>, Error> {
                Ok(self.to_be_bytes().to_vec())
            }
        }

        impl SerializeBytes for $t {
            #[inline]
            fn tls_serialize(&self) -> Result<Vec<u8>, Error> {
                <&Self as SerializeBytes>::tls_serialize(&self)
            }
        }

        impl Serialize for $t {
            #[cfg(feature = "std")]
            #[inline]
            fn tls_serialize<W: Write>(&self, writer: &mut W) -> Result<usize, Error> {
                let written = writer.write(&self.to_be_bytes())?;
                #[cfg(not(hax))]
                debug_assert_eq!(written, $bytes);
                Ok(written)
            }
        }

        impl Serialize for &$t {
            #[cfg(feature = "std")]
            #[inline]
            fn tls_serialize<W: Write>(&self, writer: &mut W) -> Result<usize, Error> {
                <$t as Serialize>::tls_serialize(self, writer)
            }
        }

        impl Size for $t {
            #[inline]
            fn tls_serialized_len(&self) -> usize {
                $bytes
            }
        }

        impl SizeChecked for $t {
            #[inline]
            fn tls_serialized_len_checked(&self) -> Option<usize> {
                Some($bytes)
            }
        }

        impl Size for &$t {
            #[inline]
            fn tls_serialized_len(&self) -> usize {
                (*self).tls_serialized_len()
            }
        }

        impl SizeChecked for &$t {
            #[inline]
            fn tls_serialized_len_checked(&self) -> Option<usize> {
                (*self).tls_serialized_len_checked()
            }
        }
    };
}

impl_unsigned!(u8, 1);
impl_unsigned!(u16, 2);
impl_unsigned!(U24, 3);
impl_unsigned!(u32, 4);
impl_unsigned!(u64, 8);

impl From<core::array::TryFromSliceError> for Error {
    fn from(_: core::array::TryFromSliceError) -> Self {
        Self::InvalidInput
    }
}

// Implement (de)serialization for tuple.
impl<T, U> Deserialize for (T, U)
where
    T: Deserialize,
    U: Deserialize,
{
    #[cfg(feature = "std")]
    #[inline(always)]
    fn tls_deserialize<R: Read>(bytes: &mut R) -> Result<Self, Error> {
        Ok((T::tls_deserialize(bytes)?, U::tls_deserialize(bytes)?))
    }
}

impl<T, U> DeserializeBytes for (T, U)
where
    T: DeserializeBytes,
    U: DeserializeBytes,
{
    #[inline(always)]
    fn tls_deserialize_bytes(bytes: &[u8]) -> Result<(Self, &[u8]), Error> {
        let (first_element, remainder) = T::tls_deserialize_bytes(bytes)?;
        let (second_element, remainder) = U::tls_deserialize_bytes(remainder)?;
        Ok(((first_element, second_element), remainder))
    }
}

impl<T, U> Serialize for (T, U)
where
    T: Serialize,
    U: Serialize,
{
    #[cfg(feature = "std")]
    #[inline(always)]
    fn tls_serialize<W: Write>(&self, writer: &mut W) -> Result<usize, Error> {
        let written = self.0.tls_serialize(writer)?;
        Ok(add!(self.1.tls_serialize(writer)?, written))
    }
}

impl<T, U> SizeChecked for (T, U)
where
    T: SizeChecked,
    U: SizeChecked,
{
    #[inline(always)]
    fn tls_serialized_len_checked(&self) -> Option<usize> {
        self.0
            .tls_serialized_len_checked()?
            .checked_add(self.1.tls_serialized_len_checked()?)
    }
}

impl<T, U> Size for (T, U)
where
    T: Size,
    U: Size,
{
    #[inline(always)]
    fn tls_serialized_len(&self) -> usize {
        hax_lib::assume!(
            self.0.tls_serialized_len().to_int() + self.1.tls_serialized_len().to_int()
                <= usize::MAX.to_int()
        );
        self.0.tls_serialized_len() + self.1.tls_serialized_len()
    }
}

impl<T, U, V> Deserialize for (T, U, V)
where
    T: Deserialize,
    U: Deserialize,
    V: Deserialize,
{
    #[cfg(feature = "std")]
    #[inline(always)]
    fn tls_deserialize<R: Read>(bytes: &mut R) -> Result<Self, Error> {
        Ok((
            T::tls_deserialize(bytes)?,
            U::tls_deserialize(bytes)?,
            V::tls_deserialize(bytes)?,
        ))
    }
}

impl<T, U, V> DeserializeBytes for (T, U, V)
where
    T: DeserializeBytes,
    U: DeserializeBytes,
    V: DeserializeBytes,
{
    #[inline(always)]
    fn tls_deserialize_bytes(bytes: &[u8]) -> Result<(Self, &[u8]), Error> {
        let (first_element, remainder) = T::tls_deserialize_bytes(bytes)?;
        let (second_element, remainder) = U::tls_deserialize_bytes(remainder)?;
        let (third_element, remainder) = V::tls_deserialize_bytes(remainder)?;
        Ok(((first_element, second_element, third_element), remainder))
    }
}

impl<T, U, V> Serialize for (T, U, V)
where
    T: Serialize,
    U: Serialize,
    V: Serialize,
{
    #[cfg(feature = "std")]
    #[inline(always)]
    fn tls_serialize<W: Write>(&self, writer: &mut W) -> Result<usize, Error> {
        let written = self.0.tls_serialize(writer)?;
        let written = add!(written, self.1.tls_serialize(writer)?);
        Ok(add!(self.2.tls_serialize(writer)?, written))
    }
}

impl<T, U, V> SizeChecked for (T, U, V)
where
    T: SizeChecked,
    U: SizeChecked,
    V: SizeChecked,
{
    #[inline(always)]
    fn tls_serialized_len_checked(&self) -> Option<usize> {
        self.0
            .tls_serialized_len_checked()?
            .checked_add(self.1.tls_serialized_len_checked()?)?
            .checked_add(self.2.tls_serialized_len_checked()?)
    }
}

impl<T, U, V> Size for (T, U, V)
where
    T: Size,
    U: Size,
    V: Size,
{
    #[inline(always)]
    fn tls_serialized_len(&self) -> usize {
        hax_lib::assume!(
            self.0.tls_serialized_len().to_int()
                + self.1.tls_serialized_len().to_int()
                + self.2.tls_serialized_len().to_int()
                <= usize::MAX.to_int()
        );
        self.0.tls_serialized_len() + self.1.tls_serialized_len() + self.2.tls_serialized_len()
    }
}

impl Size for () {
    #[inline(always)]
    fn tls_serialized_len(&self) -> usize {
        0
    }
}

impl SizeChecked for () {
    #[inline(always)]
    fn tls_serialized_len_checked(&self) -> Option<usize> {
        Some(0)
    }
}

impl Deserialize for () {
    #[cfg(feature = "std")]
    #[inline(always)]
    fn tls_deserialize<R: Read>(_: &mut R) -> Result<(), Error> {
        Ok(())
    }
}

impl DeserializeBytes for () {
    #[inline(always)]
    fn tls_deserialize_bytes(bytes: &[u8]) -> Result<(Self, &[u8]), Error> {
        Ok(((), bytes))
    }
}

impl Serialize for () {
    #[cfg(feature = "std")]
    fn tls_serialize<W: Write>(&self, _: &mut W) -> Result<usize, Error> {
        Ok(0)
    }
}

impl<T> Size for PhantomData<T> {
    #[inline(always)]
    fn tls_serialized_len(&self) -> usize {
        0
    }
}

impl<T> SizeChecked for PhantomData<T> {
    #[inline(always)]
    fn tls_serialized_len_checked(&self) -> Option<usize> {
        Some(0)
    }
}

impl<T> Deserialize for PhantomData<T> {
    #[cfg(feature = "std")]
    #[inline(always)]
    fn tls_deserialize<R: Read>(_: &mut R) -> Result<Self, Error> {
        Ok(PhantomData)
    }
}

impl<T> DeserializeBytes for PhantomData<T> {
    #[inline(always)]
    fn tls_deserialize_bytes(bytes: &[u8]) -> Result<(Self, &[u8]), Error> {
        Ok((PhantomData, bytes))
    }
}

impl<T> Serialize for PhantomData<T> {
    #[cfg(feature = "std")]
    #[inline(always)]
    fn tls_serialize<W: Write>(&self, _: &mut W) -> Result<usize, Error> {
        Ok(0)
    }
}

impl<T> SerializeBytes for PhantomData<T> {
    #[inline(always)]
    fn tls_serialize(&self) -> Result<Vec<u8>, Error> {
        Ok(vec![])
    }
}

impl<T: Size> Size for Box<T> {
    #[inline(always)]
    fn tls_serialized_len(&self) -> usize {
        self.as_ref().tls_serialized_len()
    }
}

impl<T: SizeChecked> SizeChecked for Box<T> {
    #[inline(always)]
    fn tls_serialized_len_checked(&self) -> Option<usize> {
        self.as_ref().tls_serialized_len_checked()
    }
}

impl<T: Serialize> Serialize for Box<T> {
    #[cfg(feature = "std")]
    #[inline(always)]
    fn tls_serialize<W: Write>(&self, writer: &mut W) -> Result<usize, Error> {
        self.as_ref().tls_serialize(writer)
    }
}

impl<T: SerializeBytes> SerializeBytes for Box<T> {
    #[inline(always)]
    fn tls_serialize(&self) -> Result<Vec<u8>, Error> {
        self.as_ref().tls_serialize()
    }
}

impl<T: Deserialize> Deserialize for Box<T> {
    #[cfg(feature = "std")]
    #[inline(always)]
    fn tls_deserialize<R: Read>(bytes: &mut R) -> Result<Self, Error> {
        T::tls_deserialize(bytes).map(Box::new)
    }
}

impl<T: DeserializeBytes> DeserializeBytes for Box<T> {
    #[inline(always)]
    fn tls_deserialize_bytes(bytes: &[u8]) -> Result<(Self, &[u8]), Error> {
        T::tls_deserialize_bytes(bytes).map(|(v, r)| (Box::new(v), r))
    }
}
