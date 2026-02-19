use tls_codec::{Serialize, TlsVecU32};
use tls_codec_derive::{TlsSerialize, TlsSize, TlsSizeChecked, TlsSizeOverflow};

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
    bytes: TlsVecU32<u8>,
}

const N: usize = 0xFFFF;
const ITERATIONS: usize = 20_000;

fn main() {
    let long_vec = TlsVecU32::from(vec![Inner::default(); N]);

    core::hint::black_box({
        for _ in 0..ITERATIONS {
            long_vec.tls_serialize_detached().unwrap();
        }
    });
}
