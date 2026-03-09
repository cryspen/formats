use criterion::{BatchSize, Criterion};
use criterion::{criterion_group, criterion_main};
use tls_codec::TlsByteVecU32;
use tls_codec_derive::{TlsSerialize, TlsSize, TlsSizeChecked, TlsSizeOverflow};

/// Length of the test bytes vector.
const N: usize = 0xFFFF;

#[derive(TlsSize, TlsSizeChecked, TlsSizeOverflow, TlsSerialize, Default, Clone, Copy)]
#[repr(u8)]
enum Type {
    One,

    #[default]
    Two,
}

#[derive(TlsSize, TlsSizeChecked, TlsSizeOverflow, TlsSerialize, Default, Clone)]
struct Inner {
    the_type: Type,
    bytes: TlsByteVecU32,
}

fn vector(c: &mut Criterion) {
    use tls_codec::*;
    c.bench_function("TLS Serialize Vector", |b| {
        b.iter_batched_ref(
            || (TlsVecU32::from(vec![77u8; N]), Vec::with_capacity(8 + N)),
            |(long_vec, buf)| long_vec.tls_serialize(buf).unwrap(),
            BatchSize::SmallInput,
        )
    });

    c.bench_function("TLS Deserialize Vector", |b| {
        b.iter_batched_ref(
            || {
                let long_vec = vec![77u8; N];
                TlsSliceU32(&long_vec).tls_serialize_detached().unwrap()
            },
            |serialized_long_vec| {
                TlsVecU32::<u8>::tls_deserialize(&mut serialized_long_vec.as_slice()).unwrap()
            },
            BatchSize::SmallInput,
        )
    });

    c.bench_function("TLS Serialize Vector (Inner)", |b| {
        b.iter_batched_ref(
            || TlsVecU32::from(vec![Inner::default(); N]),
            |long_vec| long_vec.tls_serialize_detached().unwrap(),
            BatchSize::SmallInput,
        )
    });
}

fn byte_vector(c: &mut Criterion) {
    use tls_codec::*;
    c.bench_function("TLS Serialize Byte Vector", |b| {
        b.iter_batched_ref(
            || {
                (
                    TlsByteVecU32::from(vec![77u8; N]),
                    Vec::with_capacity(8 + N),
                )
            },
            |(long_vec, buf)| Serialize::tls_serialize(long_vec, buf).unwrap(),
            BatchSize::SmallInput,
        )
    });
    c.bench_function("TLS Deserialize Byte Vector", |b| {
        b.iter_batched_ref(
            || {
                let long_vec = vec![77u8; N];
                TlsByteSliceU32(&long_vec).tls_serialize_detached().unwrap()
            },
            |serialized_long_vec| {
                TlsVecU32::<u8>::tls_deserialize(&mut serialized_long_vec.as_slice()).unwrap()
            },
            BatchSize::SmallInput,
        )
    });
}

fn byte_slice(c: &mut Criterion) {
    use tls_codec::*;
    c.bench_function("TLS Serialize Byte Slice", |b| {
        b.iter_batched_ref(
            || (vec![77u8; N], Vec::with_capacity(8 + N)),
            |(long_vec, buf)| TlsByteSliceU32(long_vec).tls_serialize(buf).unwrap(),
            BatchSize::SmallInput,
        )
    });
}

fn slice(c: &mut Criterion) {
    use tls_codec::*;
    c.bench_function("TLS Serialize Slice", |b| {
        b.iter_batched_ref(
            || (vec![77u8; N], Vec::with_capacity(8 + N)),
            |(long_vec, buf)| TlsSliceU32(long_vec).tls_serialize(buf).unwrap(),
            BatchSize::SmallInput,
        )
    });
}
fn benchmark(c: &mut Criterion) {
    vector(c);
    slice(c);
    byte_vector(c);
    byte_slice(c);
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
