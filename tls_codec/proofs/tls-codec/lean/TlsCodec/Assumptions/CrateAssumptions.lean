/- Crate-specific assumptions (ASSUMED axioms about this crate's types, and the opaque
length-sum helpers with their ASSUMED bound). Crate-side:
they mention crate types, so they cannot be in the `-extra-includes` modules (those are
imported by `Types.lean`). Imported by `FunsExternal.lean`, hence visible from `Funs.lean`
on. Every proof using one shows it in `#print axioms`. -/
import TlsCodec.Extraction.Types
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

namespace CoreModels

/-- ASSUMED: `U24` is `struct U24([u8; 3])` without `#[repr]`, so Rust does not
    guarantee its size; rustc lays it out in 3 bytes. -/
axiom core.mem.size_of_U24 : core.mem.size_of tls_codec.U24 = ok 3#usize

end CoreModels

/-! ## Length-sum helpers (`lib.rs`)

`tls_codec::len_add` / `tls_codec::checked_len_add` are opaque in the sandbox scenario
(`hax.toml`); their declarations live here rather than in `FunsExternal.lean`, next to the
ASSUMED bound below. Signatures exactly as in `Extraction/FunsExternal_Template.lean`.
Rust, on `target_pointer_width = "64"` (the variant extracted here):
`const fn len_add(a: usize, b: usize) -> usize { a + b }` and
`fn checked_len_add(a: usize, b: usize) -> Result<usize, Error> { Ok(a + b) }`;
on narrower targets they saturate / return `Err(InvalidVectorLength)` instead. -/

/-- [tls_codec::len_add] (opaque, `hax.toml`). -/
axiom len_add : Std.Usize → Std.Usize → RustM Std.Usize

/-- [tls_codec::checked_len_add] (opaque, `hax.toml`). -/
axiom checked_len_add
  : Std.Usize → Std.Usize → RustM (core.result.Result Std.Usize tls_codec.Error)

/-- ASSUMED: `len_add` never fails, and is the exact sum whenever it fits in `usize`.
    Justification: on 64-bit targets the operands are sums of in-memory lengths, and
    allocations are bounded by `isize::MAX`, so the Rust addition cannot overflow.
    The model allows slices of length `Usize.max`, so an unconditional
    `len_add a b = ok (a + b)` would be inconsistent; the result is only pinned down
    when the sum fits. -/
axiom len_add_spec (a b : Usize) :
  ∃ r, len_add a b = ok r ∧ (a.val + b.val ≤ Usize.max → r.val = a.val + b.val)

/-- ASSUMED: `checked_len_add` is the checked sum: `Ok (a + b)` when it fits in `usize`,
    `Err InvalidVectorLength` otherwise (owner decision "`&[T]` / `Vec` serializers",
    option 4, 2026-10-15). Exact for the non-64-bit variant
    (`a.checked_add(b).ok_or(..)`); for the 64-bit variant (`Ok(a + b)`) it agrees whenever
    the sum fits, i.e. it assumes the 64-bit addition never overflows (same justification
    as `len_add_spec`). Consistent: `checked_len_add` is an opaque constant. -/
axiom checked_len_add_spec (a b : Usize) :
  (a.val + b.val ≤ Usize.max →
     ∃ r, checked_len_add a b = ok (.Ok r) ∧ r.val = a.val + b.val) ∧
  (Usize.max < a.val + b.val →
     checked_len_add a b = ok (.Err tls_codec.Error.InvalidVectorLength))

/-! ## Platform width -/

/-- ASSUMED: `usize` is 64 bits (owner decision "64-bit `usize` for the `U24` / `U32`
    cases", option 1, 2026-10-15). The crate is used on 64-bit targets; CoreModels'
    `usize` `from_be_bytes` / `to_be_bytes` work on 8 bytes while the ASSUMED
    `size_of_Usize` follows `numBits`, so the `U24` conversions need this.
    Consistent: `System.Platform.numBits` is defined from an `opaque` (`getNumBits`). -/
axiom numBits_eq_64 : System.Platform.numBits = 64
