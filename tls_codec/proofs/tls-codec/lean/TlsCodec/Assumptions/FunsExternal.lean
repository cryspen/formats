-- [tls_codec]: external functions.
-- Seeded by hax from Extraction/FunsExternal_Template.lean: fill the holes.
-- hax never modifies this file; after re-extraction, compare it against the
-- regenerated template to see what changed.
import Aeneas
import CoreModels
import TlsCodec.Extraction.Types
import TlsCodec.Assumptions.CrateAssumptions
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048
open tls_codec

/-! Note (hand edit): the `fmt` axioms below were seeded by hax with the type
    `… → RustM ((Result Unit fmt.Error) × Formatter × (Formatter → Formatter))`.
    The extra backward function does not match `core.fmt.Debug`/`Display`'s
    `fmt` field in CoreModels (`… → RustM ((Result Unit fmt.Error) × Formatter)`),
    which is the type Extraction/Funs.lean uses them at, so it was dropped. -/

/-- [tls_codec::{impl core::fmt::Debug for tls_codec::Error}::fmt]:
    Source: 'tls_codec/src/lib.rs', lines 74:9-74:14
    Visibility: public -/
axiom Error.Insts.CoreFmtDebug.fmt
  :
  tls_codec.Error → core.fmt.Formatter → RustM ((core.result.Result Unit core.fmt.Error) ×
    core.fmt.Formatter)

/-- [tls_codec::{impl core::fmt::Display for tls_codec::Error}::fmt]:
    Source: 'tls_codec/src/lib.rs', lines 112:4-114:5
    Visibility: public -/
axiom Error.Insts.CoreFmtDisplay.fmt
  :
  tls_codec.Error → core.fmt.Formatter → RustM ((core.result.Result Unit core.fmt.Error) ×
    core.fmt.Formatter)

/-- [tls_codec::{impl core::fmt::Debug for tls_codec::U24}::fmt]:
    Source: 'tls_codec/src/lib.rs', lines 381:22-381:27
    Visibility: public -/
axiom U24.Insts.CoreFmtDebug.fmt
  :
  U24 → core.fmt.Formatter → RustM ((core.result.Result Unit core.fmt.Error) ×
    core.fmt.Formatter)

/-- [tls_codec::quic_vec::write_hex]:
    Source: 'tls_codec/src/quic_vec.rs', lines 256:0-267:1 -/
axiom quic_vec.write_hex
  :
  core.fmt.Formatter → Slice Std.U8 → RustM ((core.result.Result Unit core.fmt.Error) ×
    core.fmt.Formatter)

/-- [tls_codec::quic_vec::{impl core::fmt::Debug for tls_codec::quic_vec::VLBytes}::fmt]:
    Source: 'tls_codec/src/quic_vec.rs', lines 272:12-276:13
    Visibility: public -/
axiom quic_vec.VLBytes.Insts.CoreFmtDebug.fmt
  :
  quic_vec.VLBytes → core.fmt.Formatter → RustM ((core.result.Result Unit core.fmt.Error) ×
    core.fmt.Formatter)

/-- [tls_codec::quic_vec::{impl core::fmt::Debug for tls_codec::quic_vec::VLByteVec}::fmt]:
    Source: 'tls_codec/src/quic_vec.rs', lines 272:12-276:13
    Visibility: public -/
axiom quic_vec.VLByteVec.Insts.CoreFmtDebug.fmt
  :
  quic_vec.VLByteVec → core.fmt.Formatter → RustM ((core.result.Result Unit core.fmt.Error) ×
    core.fmt.Formatter)

/-- [tls_codec::quic_vec::{impl core::fmt::Debug for tls_codec::quic_vec::VLByteSlice<'_0>}::fmt]:
    Source: 'tls_codec/src/quic_vec.rs', lines 616:4-620:5
    Visibility: public -/
axiom quic_vec.VLByteSlice.Insts.CoreFmtDebug.fmt
  :
  quic_vec.VLByteSlice → core.fmt.Formatter → RustM ((core.result.Result Unit core.fmt.Error) ×
    core.fmt.Formatter)

/-- [tls_codec::tls_vec::{impl core::fmt::Debug for tls_codec::tls_vec::TlsVecU8<T>}::fmt]:
    Source: 'tls_codec/src/tls_vec.rs', lines 528:21-528:26
    Visibility: public -/
axiom tls_vec.TlsVecU8.Insts.CoreFmtDebug.fmt
  {T : Type} (corefmtDebugInst : core.fmt.Debug T) :
  tls_vec.TlsVecU8 T → core.fmt.Formatter → RustM ((core.result.Result Unit core.fmt.Error) ×
    core.fmt.Formatter)

/-- [tls_codec::tls_vec::{impl core::fmt::Debug for tls_codec::tls_vec::TlsVecU16<T>}::fmt]:
    Source: 'tls_codec/src/tls_vec.rs', lines 528:21-528:26
    Visibility: public -/
axiom tls_vec.TlsVecU16.Insts.CoreFmtDebug.fmt
  {T : Type} (corefmtDebugInst : core.fmt.Debug T) :
  tls_vec.TlsVecU16 T → core.fmt.Formatter → RustM ((core.result.Result Unit core.fmt.Error) ×
    core.fmt.Formatter)

/-- [tls_codec::tls_vec::{impl core::fmt::Debug for tls_codec::tls_vec::TlsVecU24<T>}::fmt]:
    Source: 'tls_codec/src/tls_vec.rs', lines 528:21-528:26
    Visibility: public -/
axiom tls_vec.TlsVecU24.Insts.CoreFmtDebug.fmt
  {T : Type} (corefmtDebugInst : core.fmt.Debug T) :
  tls_vec.TlsVecU24 T → core.fmt.Formatter → RustM ((core.result.Result Unit core.fmt.Error) ×
    core.fmt.Formatter)

/-- [tls_codec::tls_vec::{impl core::fmt::Debug for tls_codec::tls_vec::TlsVecU32<T>}::fmt]:
    Source: 'tls_codec/src/tls_vec.rs', lines 528:21-528:26
    Visibility: public -/
axiom tls_vec.TlsVecU32.Insts.CoreFmtDebug.fmt
  {T : Type} (corefmtDebugInst : core.fmt.Debug T) :
  tls_vec.TlsVecU32 T → core.fmt.Formatter → RustM ((core.result.Result Unit core.fmt.Error) ×
    core.fmt.Formatter)

/-- [tls_codec::tls_vec::{impl core::fmt::Debug for tls_codec::tls_vec::SecretTlsVecU8<T>}::fmt]:
    Source: 'tls_codec/src/tls_vec.rs', lines 528:21-528:26
    Visibility: public -/
axiom tls_vec.SecretTlsVecU8.Insts.CoreFmtDebug.fmt
  {T : Type} (corefmtDebugInst : core.fmt.Debug T) (zeroizeZeroizeInst :
  zeroize.Zeroize T) :
  tls_vec.SecretTlsVecU8 T → core.fmt.Formatter → RustM ((core.result.Result Unit core.fmt.Error) ×
    core.fmt.Formatter)

/-- [tls_codec::tls_vec::{impl core::fmt::Debug for tls_codec::tls_vec::SecretTlsVecU16<T>}::fmt]:
    Source: 'tls_codec/src/tls_vec.rs', lines 528:21-528:26
    Visibility: public -/
axiom tls_vec.SecretTlsVecU16.Insts.CoreFmtDebug.fmt
  {T : Type} (corefmtDebugInst : core.fmt.Debug T) (zeroizeZeroizeInst :
  zeroize.Zeroize T) :
  tls_vec.SecretTlsVecU16 T → core.fmt.Formatter → RustM ((core.result.Result Unit core.fmt.Error) ×
    core.fmt.Formatter)

/-- [tls_codec::tls_vec::{impl core::fmt::Debug for tls_codec::tls_vec::SecretTlsVecU24<T>}::fmt]:
    Source: 'tls_codec/src/tls_vec.rs', lines 528:21-528:26
    Visibility: public -/
axiom tls_vec.SecretTlsVecU24.Insts.CoreFmtDebug.fmt
  {T : Type} (corefmtDebugInst : core.fmt.Debug T) (zeroizeZeroizeInst :
  zeroize.Zeroize T) :
  tls_vec.SecretTlsVecU24 T → core.fmt.Formatter → RustM ((core.result.Result Unit core.fmt.Error) ×
    core.fmt.Formatter)

/-- [tls_codec::tls_vec::{impl core::fmt::Debug for tls_codec::tls_vec::SecretTlsVecU32<T>}::fmt]:
    Source: 'tls_codec/src/tls_vec.rs', lines 528:21-528:26
    Visibility: public -/
axiom tls_vec.SecretTlsVecU32.Insts.CoreFmtDebug.fmt
  {T : Type} (corefmtDebugInst : core.fmt.Debug T) (zeroizeZeroizeInst :
  zeroize.Zeroize T) :
  tls_vec.SecretTlsVecU32 T → core.fmt.Formatter → RustM ((core.result.Result Unit core.fmt.Error) ×
    core.fmt.Formatter)

/-- [tls_codec::tls_vec::{impl core::fmt::Debug for tls_codec::tls_vec::TlsByteVecU8}::fmt]:
    Source: 'tls_codec/src/tls_vec.rs', lines 734:28-734:33
    Visibility: public -/
axiom tls_vec.TlsByteVecU8.Insts.CoreFmtDebug.fmt
  :
  tls_vec.TlsByteVecU8 → core.fmt.Formatter → RustM ((core.result.Result Unit core.fmt.Error) ×
    core.fmt.Formatter)

/-- [tls_codec::tls_vec::{impl core::fmt::Debug for tls_codec::tls_vec::TlsByteVecU16}::fmt]:
    Source: 'tls_codec/src/tls_vec.rs', lines 734:28-734:33
    Visibility: public -/
axiom tls_vec.TlsByteVecU16.Insts.CoreFmtDebug.fmt
  :
  tls_vec.TlsByteVecU16 → core.fmt.Formatter → RustM ((core.result.Result Unit core.fmt.Error) ×
    core.fmt.Formatter)

/-- [tls_codec::tls_vec::{impl core::fmt::Debug for tls_codec::tls_vec::TlsByteVecU24}::fmt]:
    Source: 'tls_codec/src/tls_vec.rs', lines 734:28-734:33
    Visibility: public -/
axiom tls_vec.TlsByteVecU24.Insts.CoreFmtDebug.fmt
  :
  tls_vec.TlsByteVecU24 → core.fmt.Formatter → RustM ((core.result.Result Unit core.fmt.Error) ×
    core.fmt.Formatter)

/-- [tls_codec::tls_vec::{impl core::fmt::Debug for tls_codec::tls_vec::TlsByteVecU32}::fmt]:
    Source: 'tls_codec/src/tls_vec.rs', lines 734:28-734:33
    Visibility: public -/
axiom tls_vec.TlsByteVecU32.Insts.CoreFmtDebug.fmt
  :
  tls_vec.TlsByteVecU32 → core.fmt.Formatter → RustM ((core.result.Result Unit core.fmt.Error) ×
    core.fmt.Formatter)

/-- [tls_codec::varint::{impl core::fmt::Debug for tls_codec::varint::TlsVarInt}::fmt]:
    Source: 'tls_codec/src/varint.rs', lines 6:9-6:14
    Visibility: public -/
axiom varint.TlsVarInt.Insts.CoreFmtDebug.fmt
  :
  varint.TlsVarInt → core.fmt.Formatter → RustM ((core.result.Result Unit core.fmt.Error) ×
    core.fmt.Formatter)

/-! ## Hand-translated bodies of the `opaque` crate items (not extracted)

`hax.toml` makes these items opaque because aeneas cannot translate
`Iterator::try_fold` (excluded) or, for `Box`, the `map` closure. Each `def`
below has exactly the name and type of the signature-only `axiom` hax seeded in
the template, and translates the Rust body by hand, in the shape aeneas gives
comparable code in `Extraction/Funs.lean` (`?` as `branch` / `from_residual`,
loops as `loop` over `cont` / `done`, slice iteration via CoreModels'
`Slice::iter` and `Iter::next`). Build: `cfg(hax)` on, `cfg(fuzzing)` off,
debug assertions on (hax extracts the dev profile). The length sums call the
opaque `checked_len_add` of `CrateAssumptions.lean` (64-bit semantics, ASSUMED bound
`checked_len_add_spec`), exactly as the extracted code does.

This file is compiled before `Extraction/Funs.lean`, so the crate functions
these bodies call are not visible here. `tls_codec.Copied` holds verbatim copies
of them (same text as `Extraction/Funs.lean`, attributes other than `@[reducible]`
dropped; names resolve
to the copies inside the namespace). `Verification/Helpers.lean`
proves each copy equal to its original (`tls_codec.Copied.*_eq`), so the copies
add nothing to the trusted base. -/

noncomputable section

namespace tls_codec.Copied

/-- Copy of `checked_capacity` (Extraction/Funs.lean:375). -/
def checked_capacity
  (len : Std.Usize) : RustM (core.result.Result Std.Usize Error) := do
  let i ← lift (IScalar.hcast .Usize core.num.Isize.MAX)
  if len > i
  then ok (core.result.Result.Err Error.InvalidVectorLength)
  else ok (core.result.Result.Ok len)

/-- Copy of `checked_alloc_len` (Extraction/Funs.lean:384). -/
def checked_alloc_len
  (a : Std.Usize) (b : Std.Usize) :
  RustM (core.result.Result Std.Usize Error)
  := do
  let i ← core.num.Usize.saturating_add a b
  checked_capacity i

/-- Copy of `U24.MAX` (Extraction/Funs.lean:552). -/
def U24.MAX : U24 := let a := Array.repeat 3#usize 255#u8
                     a

/-- Copy of `FromUsizeU24.from.LEN` (Extraction/Funs.lean:565). -/
def FromUsizeU24.from.LEN : RustM Std.Usize := core.mem.size_of Std.Usize

/-- Copy of `Usize.Insts.CoreConvertFromU24.from` (Extraction/Funs.lean:570). -/
def Usize.Insts.CoreConvertFromU24.from (value : U24) : RustM Std.Usize := do
  let usize_bytes := Array.repeat 8#usize 0#u8
  let i ← FromUsizeU24.from.LEN
  let i1 ← i - 3#usize
  let (s, index_mut_back) ←
    core.Array.Insts.CoreOpsIndexIndexMut.index_mut
      (core.Slice.Insts.CoreOpsIndexIndexMut
      (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
      Std.U8)) usize_bytes { start := i1 }
  let s1 ← lift (Array.to_slice value)
  let s2 ← core.slice.Slice.copy_from_slice core.U8.Insts.CoreMarkerCopy s s1
  let usize_bytes1 := index_mut_back s2
  core.num.Usize.from_be_bytes usize_bytes1

/-- Copy of `Usize.Insts.CoreConvertFromU24` (Extraction/Funs.lean:587). -/
@[reducible]
def Usize.Insts.CoreConvertFromU24 : core.convert.From Std.Usize U24 := {
  «from» := Usize.Insts.CoreConvertFromU24.from
}

/-- Copy of `U8.Insts.Tls_codecSize.tls_serialized_len` (Extraction/Funs.lean:1049). -/
def U8.Insts.Tls_codecSize.tls_serialized_len
  (self : Std.U8) : RustM Std.Usize := do
  ok 1#usize

/-- Copy of `quic_vec.MAX_MLS_LEN` (Extraction/Funs.lean:2440). -/
def quic_vec.MAX_MLS_LEN : RustM Std.U64 := do
  let i ← 1#u64 <<< 30#i32
  i - 1#u64

/-- Copy of `varint.TlsVarInt.value` (Extraction/Funs.lean:2447). -/
def varint.TlsVarInt.value (self : varint.TlsVarInt) : RustM Std.U64 := do
  ok self

/-- Copy of `quic_vec.ContentLength.MAX` (Extraction/Funs.lean:2477). -/
def quic_vec.ContentLength.MAX : RustM Std.U64 := quic_vec.MAX_MLS_LEN

/-- Copy of `quic_vec.ContentLength.new` (Extraction/Funs.lean:2481). -/
def quic_vec.ContentLength.new
  (value : varint.TlsVarInt) :
  RustM (core.result.Result quic_vec.ContentLength Error)
  := do
  let i ← varint.TlsVarInt.value value
  let i1 ← quic_vec.ContentLength.MAX
  if i1 < i
  then ok (core.result.Result.Err Error.InvalidVectorLength)
  else ok (core.result.Result.Ok value)

/-- Copy of `varint.TlsVarInt.MAX` (Extraction/Funs.lean:2495). -/
def varint.TlsVarInt.MAX : RustM Std.U64 := do
  let i ← 1#u64 <<< 62#i32
  i - 1#u64

/-- Copy of `varint.TlsVarInt.try_new` (Extraction/Funs.lean:2501). -/
def varint.TlsVarInt.try_new
  (value : Std.U64) : RustM (core.result.Result varint.TlsVarInt Error) := do
  let i ← varint.TlsVarInt.MAX
  if i < value
  then ok (core.result.Result.Err Error.InvalidVectorLength)
  else ok (core.result.Result.Ok value)

/-- Copy of `Error.Insts.CoreConvertFromTryFromIntError.from` (Extraction/Funs.lean:2511). -/
def Error.Insts.CoreConvertFromTryFromIntError.from
  (_e : core.num.error.TryFromIntError) : RustM Error := do
  ok Error.InvalidVectorLength

/-- Copy of `Error.Insts.CoreConvertFromTryFromIntError` (Extraction/Funs.lean:2518). -/
@[reducible]
def Error.Insts.CoreConvertFromTryFromIntError : core.convert.From Error
  core.num.error.TryFromIntError := {
  «from» := Error.Insts.CoreConvertFromTryFromIntError.from
}

/-- Copy of `quic_vec.ContentLength.from_usize` (Extraction/Funs.lean:2525). -/
def quic_vec.ContentLength.from_usize
  (value : Std.Usize) :
  RustM (core.result.Result quic_vec.ContentLength Error)
  := do
  let r ←
    core.U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from value
  let cf ← core.result.Result.Insts.CoreOpsTry_traitTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ← varint.TlsVarInt.try_new val
    let cf1 ← core.result.Result.Insts.CoreOpsTry_traitTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      quic_vec.ContentLength.new val1
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
        quic_vec.ContentLength (core.convert.From.Blanket Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
      quic_vec.ContentLength Error.Insts.CoreConvertFromTryFromIntError
      residual

/-- Copy of `varint.TlsVarInt.bytes_len` (Extraction/Funs.lean:2549). -/
def varint.TlsVarInt.bytes_len
  (self : varint.TlsVarInt) : RustM Std.Usize := do
  if self <= 63#u64
  then ok 1#usize
  else
    if self <= 16383#u64
    then ok 2#usize
    else if self <= 1073741823#u64
         then ok 4#usize
         else ok 8#usize

/-- Copy of `varint.TlsVarInt.write_bytes_loop0.body` (Extraction/Funs.lean:3175). -/
def varint.TlsVarInt.write_bytes_loop0.body
  (bytes : Slice Std.U8) (value : Std.U64) (i : Std.Usize) :
  RustM (ControlFlow ((Slice Std.U8) × Std.U64 × Std.Usize) (Slice Std.U8))
  := do
  if i > 0#usize
  then
    let i1 ← i - 1#usize
    let i2 ← lift (value &&& 255#u64)
    let i3 ← lift (UScalar.cast .U8 i2)
    let i4 ← Slice.index_usize bytes i1
    let i5 ← lift (i4 ||| i3)
    let s ← Slice.update bytes i1 i5
    let value1 ← value >>> 8#i32
    ok (cont (s, value1, i1))
  else ok (done bytes)

/-- Copy of `varint.TlsVarInt.write_bytes_loop0` (Extraction/Funs.lean:3194). -/
def varint.TlsVarInt.write_bytes_loop0
  (bytes : Slice Std.U8) (value : Std.U64) (i : Std.Usize) :
  RustM (Slice Std.U8)
  := do
  loop
    (fun (bytes1, value1, i1) => varint.TlsVarInt.write_bytes_loop0.body bytes1
      value1 i1)
    (bytes, value, i)

/-- Copy of `varint.TlsVarInt.write_bytes_loop1.body` (Extraction/Funs.lean:3206). -/
def varint.TlsVarInt.write_bytes_loop1.body
  (bytes : Slice Std.U8) (value : Std.U64) (i : Std.Usize) :
  RustM (ControlFlow ((Slice Std.U8) × Std.U64 × Std.Usize) (Slice Std.U8))
  := do
  if i > 0#usize
  then
    let i1 ← i - 1#usize
    let i2 ← lift (value &&& 255#u64)
    let i3 ← lift (UScalar.cast .U8 i2)
    let i4 ← Slice.index_usize bytes i1
    let i5 ← lift (i4 ||| i3)
    let s ← Slice.update bytes i1 i5
    let value1 ← value >>> 8#i32
    ok (cont (s, value1, i1))
  else ok (done bytes)

/-- Copy of `varint.TlsVarInt.write_bytes_loop1` (Extraction/Funs.lean:3225). -/
def varint.TlsVarInt.write_bytes_loop1
  (bytes : Slice Std.U8) (value : Std.U64) (i : Std.Usize) :
  RustM (Slice Std.U8)
  := do
  loop
    (fun (bytes1, value1, i1) => varint.TlsVarInt.write_bytes_loop1.body bytes1
      value1 i1)
    (bytes, value, i)

/-- Copy of `varint.TlsVarInt.write_bytes_loop2.body` (Extraction/Funs.lean:3237). -/
def varint.TlsVarInt.write_bytes_loop2.body
  (bytes : Slice Std.U8) (value : Std.U64) (i : Std.Usize) :
  RustM (ControlFlow ((Slice Std.U8) × Std.U64 × Std.Usize) (Slice Std.U8))
  := do
  if i > 0#usize
  then
    let i1 ← i - 1#usize
    let i2 ← lift (value &&& 255#u64)
    let i3 ← lift (UScalar.cast .U8 i2)
    let i4 ← Slice.index_usize bytes i1
    let i5 ← lift (i4 ||| i3)
    let s ← Slice.update bytes i1 i5
    let value1 ← value >>> 8#i32
    ok (cont (s, value1, i1))
  else ok (done bytes)

/-- Copy of `varint.TlsVarInt.write_bytes_loop2` (Extraction/Funs.lean:3256). -/
def varint.TlsVarInt.write_bytes_loop2
  (bytes : Slice Std.U8) (value : Std.U64) (i : Std.Usize) :
  RustM (Slice Std.U8)
  := do
  loop
    (fun (bytes1, value1, i1) => varint.TlsVarInt.write_bytes_loop2.body bytes1
      value1 i1)
    (bytes, value, i)

/-- Copy of `varint.TlsVarInt.write_bytes_loop3.body` (Extraction/Funs.lean:3268). -/
def varint.TlsVarInt.write_bytes_loop3.body
  (bytes : Slice Std.U8) (value : Std.U64) (i : Std.Usize) :
  RustM (ControlFlow ((Slice Std.U8) × Std.U64 × Std.Usize) (Slice Std.U8))
  := do
  if i > 0#usize
  then
    let i1 ← i - 1#usize
    let i2 ← lift (value &&& 255#u64)
    let i3 ← lift (UScalar.cast .U8 i2)
    let i4 ← Slice.index_usize bytes i1
    let i5 ← lift (i4 ||| i3)
    let s ← Slice.update bytes i1 i5
    let value1 ← value >>> 8#i32
    ok (cont (s, value1, i1))
  else ok (done bytes)

/-- Copy of `varint.TlsVarInt.write_bytes_loop3` (Extraction/Funs.lean:3287). -/
def varint.TlsVarInt.write_bytes_loop3
  (bytes : Slice Std.U8) (value : Std.U64) (i : Std.Usize) :
  RustM (Slice Std.U8)
  := do
  loop
    (fun (bytes1, value1, i1) => varint.TlsVarInt.write_bytes_loop3.body bytes1
      value1 i1)
    (bytes, value, i)

/-- Copy of `varint.TlsVarInt.write_bytes` (Extraction/Funs.lean:3298). -/
def varint.TlsVarInt.write_bytes
  (self : varint.TlsVarInt) (buf : Slice Std.U8) :
  RustM ((core.result.Result Std.Usize Error) × (Slice Std.U8))
  := do
  let len ← varint.TlsVarInt.bytes_len self
  let i ← core.slice.Slice.len buf
  if i < len
  then ok (core.result.Result.Err Error.InvalidVectorLength, buf)
  else
    let (bytes, index_mut_back) ←
      core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
        (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
        Std.U8) buf { «end» := len }
    match len.val with
    | 1 =>
      let s ← Slice.update bytes 0#usize 0#u8
      let bytes1 ← varint.TlsVarInt.write_bytes_loop0 s self 1#usize
      let buf1 := index_mut_back bytes1
      ok (core.result.Result.Ok 1#usize, buf1)
    | 2 =>
      let s ← Slice.update bytes 0#usize 64#u8
      let bytes1 ← varint.TlsVarInt.write_bytes_loop1 s self 2#usize
      let buf1 := index_mut_back bytes1
      ok (core.result.Result.Ok 2#usize, buf1)
    | 4 =>
      let s ← Slice.update bytes 0#usize 128#u8
      let bytes1 ← varint.TlsVarInt.write_bytes_loop2 s self 4#usize
      let buf1 := index_mut_back bytes1
      ok (core.result.Result.Ok 4#usize, buf1)
    | 8 =>
      let s ← Slice.update bytes 0#usize 192#u8
      let bytes1 ← varint.TlsVarInt.write_bytes_loop3 s self 8#usize
      let buf1 := index_mut_back bytes1
      ok (core.result.Result.Ok 8#usize, buf1)
    | _ =>
      let a ←
        core.fmt.rt.Argument.new_display core.Usize.Insts.CoreFmtDisplay len
      let _ ←
        core.fmt.Arguments.new
          (Array.make 22#usize [
            19#u8, 73#u8, 110#u8, 118#u8, 97#u8, 108#u8, 105#u8, 100#u8, 32#u8,
            118#u8, 97#u8, 114#u8, 105#u8, 110#u8, 116#u8, 32#u8, 108#u8,
            101#u8, 110#u8, 32#u8, 192#u8, 0#u8
            ]) (Array.make 1#usize [ a ])
      fail panic

end tls_codec.Copied


/-- Hand-translated (not extracted):
    [tls_codec::tls_vec::{tls_codec::tls_vec::TlsByteVecU8}::get_content_lengths],
    'tls_codec/src/tls_vec.rs', lines 250:12-274:13 (macro `impl_serialize_common!`,
    instantiated by `impl_tls_byte_vec!(u8, TlsByteVecU8, 1)`, tls_vec.rs:985-988);
    aeneas cannot translate `Iterator::try_fold`.

    ```rust
                        || res.is_ok_and(|(total, content)| total == content + $len_len)))]
                $(#[$std_enabled])?
                fn get_content_lengths(&$self) -> Result<(usize, usize), Error> {
                    // Sum the element lengths with an overflow check on platforms where
                    // `usize` is narrow enough for it to matter (see `crate::len_add`).
                    // Computing `byte_length` directly (rather than deriving it from
                    // `tls_serialized_len()`) lets us reject a true overflow instead of
                    // trusting a possibly-saturated value from the `Size` impl.
                    let byte_length = $self
                        .as_slice()
                        .iter()
                        .try_fold(0usize, |acc, e| crate::checked_len_add(acc, e.tls_serialized_len()))?;
                    let tls_serialized_len = crate::checked_len_add(byte_length, $len_len)?;

                    let max_len = <$size>::MAX.try_into().unwrap();
                    #[cfg(not(hax))]
                    debug_assert!(
                        byte_length <= max_len,
                        "Vector length can't be encoded in the vector length a {} >= {}",
                        byte_length,
                        max_len
                    );
                    if byte_length > max_len {
                        return Err(Error::InvalidVectorLength);
                    }
                    Ok((tls_serialized_len, byte_length))
                }
    ```
    with `$self = self`, `$size = u8`, `$len_len = 1`.

    - `as_slice()` is inlined (its body is the one CoreModels call `deref self.vec`).
    - `try_fold` follows std (`while let Some(x) = self.next() { accum = f(accum, x)?; }
      try { accum }`): elements in order, the closure's `?` returns the first `Err`
      unchanged (`from_residual` with the identity `From`). The element method is
      `<u8 as Size>::tls_serialized_len` (`e : &u8`).
    - `u8::MAX.try_into()` is `<usize as TryFrom<u8>>` from `From<u8> for usize` (error `Infallible`), as aeneas translates `type_len.try_into().unwrap()` in `TlsByteVecU8.deserialize_bytes_bytes`.
    - `debug_assert!` is gated by `#[cfg(not(hax))]`, so it is not in the model: the
      `InvalidVectorLength` return handles `byte_length > max_len`. -/
def tls_vec.TlsByteVecU8.get_content_lengths
  (self : tls_vec.TlsByteVecU8) :
  RustM (core.result.Result (Std.Usize × Std.Usize) tls_codec.Error) := do
  let s ← alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref self.vec
  let i ← core.slice.Slice.iter s
  let r ←
    loop
      (fun (p : core.slice.iter.Iter Std.U8 × Std.Usize) => do
        let (o, iter1) ←
          core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next p.1
        match o with
        | core.option.Option.Some e =>
          let i1 ← tls_codec.Copied.U8.Insts.Tls_codecSize.tls_serialized_len e
          let r1 ← checked_len_add p.2 i1
          let cf ← core.result.Result.Insts.CoreOpsTry_traitTry.branch r1
          match cf with
          | core.ops.control_flow.ControlFlow.Continue acc1 => ok (cont (iter1, acc1))
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r2 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
                Std.Usize (core.convert.From.Blanket tls_codec.Error) residual
            ok (done r2)
        | core.option.Option.None => ok (done (core.result.Result.Ok p.2)))
      (i, 0#usize)
  let cf ← core.result.Result.Insts.CoreOpsTry_traitTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue byte_length =>
    let r1 ← checked_len_add byte_length 1#usize
    let cf1 ← core.result.Result.Insts.CoreOpsTry_traitTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue tls_serialized_len =>
      let r2 ←
        core.convert.TryFromTUInfallible.Blanket.try_from
          (core.convert.Into.Blanket core.Usize.Insts.CoreConvertFromU8) core.num.U8.MAX
      let max_len ←
        core.result.Result.unwrap core.convert.Infallible.Insts.CoreFmtDebug r2
      if byte_length > max_len
      then ok (core.result.Result.Err tls_codec.Error.InvalidVectorLength)
      else ok (core.result.Result.Ok (tls_serialized_len, byte_length))
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
        (Std.Usize × Std.Usize) (core.convert.From.Blanket tls_codec.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
      (Std.Usize × Std.Usize) (core.convert.From.Blanket tls_codec.Error) residual


/-- Hand-translated (not extracted):
    [tls_codec::tls_vec::{tls_codec::tls_vec::TlsByteVecU16}::get_content_lengths],
    'tls_codec/src/tls_vec.rs', lines 250:12-274:13 (macro `impl_serialize_common!`,
    instantiated by `impl_tls_byte_vec!(u16, TlsByteVecU16, 2)`, tls_vec.rs:985-988);
    aeneas cannot translate `Iterator::try_fold`.

    ```rust
                        || res.is_ok_and(|(total, content)| total == content + $len_len)))]
                $(#[$std_enabled])?
                fn get_content_lengths(&$self) -> Result<(usize, usize), Error> {
                    // Sum the element lengths with an overflow check on platforms where
                    // `usize` is narrow enough for it to matter (see `crate::len_add`).
                    // Computing `byte_length` directly (rather than deriving it from
                    // `tls_serialized_len()`) lets us reject a true overflow instead of
                    // trusting a possibly-saturated value from the `Size` impl.
                    let byte_length = $self
                        .as_slice()
                        .iter()
                        .try_fold(0usize, |acc, e| crate::checked_len_add(acc, e.tls_serialized_len()))?;
                    let tls_serialized_len = crate::checked_len_add(byte_length, $len_len)?;

                    let max_len = <$size>::MAX.try_into().unwrap();
                    #[cfg(not(hax))]
                    debug_assert!(
                        byte_length <= max_len,
                        "Vector length can't be encoded in the vector length a {} >= {}",
                        byte_length,
                        max_len
                    );
                    if byte_length > max_len {
                        return Err(Error::InvalidVectorLength);
                    }
                    Ok((tls_serialized_len, byte_length))
                }
    ```
    with `$self = self`, `$size = u16`, `$len_len = 2`.

    - `as_slice()` is inlined (its body is the one CoreModels call `deref self.vec`).
    - `try_fold` follows std (`while let Some(x) = self.next() { accum = f(accum, x)?; }
      try { accum }`): elements in order, the closure's `?` returns the first `Err`
      unchanged (`from_residual` with the identity `From`). The element method is
      `<u8 as Size>::tls_serialized_len` (`e : &u8`).
    - `u16::MAX.try_into()` is `<usize as TryFrom<u16>>` from `From<u16> for usize` (error `Infallible`), as aeneas translates `type_len.try_into().unwrap()` in `TlsByteVecU16.deserialize_bytes_bytes`.
    - `debug_assert!` is gated by `#[cfg(not(hax))]`, so it is not in the model: the
      `InvalidVectorLength` return handles `byte_length > max_len`. -/
def tls_vec.TlsByteVecU16.get_content_lengths
  (self : tls_vec.TlsByteVecU16) :
  RustM (core.result.Result (Std.Usize × Std.Usize) tls_codec.Error) := do
  let s ← alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref self.vec
  let i ← core.slice.Slice.iter s
  let r ←
    loop
      (fun (p : core.slice.iter.Iter Std.U8 × Std.Usize) => do
        let (o, iter1) ←
          core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next p.1
        match o with
        | core.option.Option.Some e =>
          let i1 ← tls_codec.Copied.U8.Insts.Tls_codecSize.tls_serialized_len e
          let r1 ← checked_len_add p.2 i1
          let cf ← core.result.Result.Insts.CoreOpsTry_traitTry.branch r1
          match cf with
          | core.ops.control_flow.ControlFlow.Continue acc1 => ok (cont (iter1, acc1))
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r2 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
                Std.Usize (core.convert.From.Blanket tls_codec.Error) residual
            ok (done r2)
        | core.option.Option.None => ok (done (core.result.Result.Ok p.2)))
      (i, 0#usize)
  let cf ← core.result.Result.Insts.CoreOpsTry_traitTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue byte_length =>
    let r1 ← checked_len_add byte_length 2#usize
    let cf1 ← core.result.Result.Insts.CoreOpsTry_traitTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue tls_serialized_len =>
      let r2 ←
        core.convert.TryFromTUInfallible.Blanket.try_from
          (core.convert.Into.Blanket core.Usize.Insts.CoreConvertFromU16) core.num.U16.MAX
      let max_len ←
        core.result.Result.unwrap core.convert.Infallible.Insts.CoreFmtDebug r2
      if byte_length > max_len
      then ok (core.result.Result.Err tls_codec.Error.InvalidVectorLength)
      else ok (core.result.Result.Ok (tls_serialized_len, byte_length))
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
        (Std.Usize × Std.Usize) (core.convert.From.Blanket tls_codec.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
      (Std.Usize × Std.Usize) (core.convert.From.Blanket tls_codec.Error) residual


/-- Hand-translated (not extracted):
    [tls_codec::tls_vec::{tls_codec::tls_vec::TlsByteVecU24}::get_content_lengths],
    'tls_codec/src/tls_vec.rs', lines 250:12-274:13 (macro `impl_serialize_common!`,
    instantiated by `impl_tls_byte_vec!(U24, TlsByteVecU24, 3)`, tls_vec.rs:985-988);
    aeneas cannot translate `Iterator::try_fold`.

    ```rust
                        || res.is_ok_and(|(total, content)| total == content + $len_len)))]
                $(#[$std_enabled])?
                fn get_content_lengths(&$self) -> Result<(usize, usize), Error> {
                    // Sum the element lengths with an overflow check on platforms where
                    // `usize` is narrow enough for it to matter (see `crate::len_add`).
                    // Computing `byte_length` directly (rather than deriving it from
                    // `tls_serialized_len()`) lets us reject a true overflow instead of
                    // trusting a possibly-saturated value from the `Size` impl.
                    let byte_length = $self
                        .as_slice()
                        .iter()
                        .try_fold(0usize, |acc, e| crate::checked_len_add(acc, e.tls_serialized_len()))?;
                    let tls_serialized_len = crate::checked_len_add(byte_length, $len_len)?;

                    let max_len = <$size>::MAX.try_into().unwrap();
                    #[cfg(not(hax))]
                    debug_assert!(
                        byte_length <= max_len,
                        "Vector length can't be encoded in the vector length a {} >= {}",
                        byte_length,
                        max_len
                    );
                    if byte_length > max_len {
                        return Err(Error::InvalidVectorLength);
                    }
                    Ok((tls_serialized_len, byte_length))
                }
    ```
    with `$self = self`, `$size = U24`, `$len_len = 3`.

    - `as_slice()` is inlined (its body is the one CoreModels call `deref self.vec`).
    - `try_fold` follows std (`while let Some(x) = self.next() { accum = f(accum, x)?; }
      try { accum }`): elements in order, the closure's `?` returns the first `Err`
      unchanged (`from_residual` with the identity `From`). The element method is
      `<u8 as Size>::tls_serialized_len` (`e : &u8`).
    - `U24::MAX.try_into()` goes through the crate's `From<U24> for usize` (lib.rs:405, copied), as aeneas translates `type_len.try_into().unwrap()` in `TlsByteVecU24.deserialize_bytes_bytes`; in the model that impl needs `System.Platform.numBits = 64` not to panic.
    - `debug_assert!` is gated by `#[cfg(not(hax))]`, so it is not in the model: the
      `InvalidVectorLength` return handles `byte_length > max_len`. -/
def tls_vec.TlsByteVecU24.get_content_lengths
  (self : tls_vec.TlsByteVecU24) :
  RustM (core.result.Result (Std.Usize × Std.Usize) tls_codec.Error) := do
  let s ← alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref self.vec
  let i ← core.slice.Slice.iter s
  let r ←
    loop
      (fun (p : core.slice.iter.Iter Std.U8 × Std.Usize) => do
        let (o, iter1) ←
          core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next p.1
        match o with
        | core.option.Option.Some e =>
          let i1 ← tls_codec.Copied.U8.Insts.Tls_codecSize.tls_serialized_len e
          let r1 ← checked_len_add p.2 i1
          let cf ← core.result.Result.Insts.CoreOpsTry_traitTry.branch r1
          match cf with
          | core.ops.control_flow.ControlFlow.Continue acc1 => ok (cont (iter1, acc1))
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r2 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
                Std.Usize (core.convert.From.Blanket tls_codec.Error) residual
            ok (done r2)
        | core.option.Option.None => ok (done (core.result.Result.Ok p.2)))
      (i, 0#usize)
  let cf ← core.result.Result.Insts.CoreOpsTry_traitTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue byte_length =>
    let r1 ← checked_len_add byte_length 3#usize
    let cf1 ← core.result.Result.Insts.CoreOpsTry_traitTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue tls_serialized_len =>
      let r2 ←
        core.convert.TryFromTUInfallible.Blanket.try_from
          (core.convert.Into.Blanket tls_codec.Copied.Usize.Insts.CoreConvertFromU24)
          tls_codec.Copied.U24.MAX
      let max_len ←
        core.result.Result.unwrap core.convert.Infallible.Insts.CoreFmtDebug r2
      if byte_length > max_len
      then ok (core.result.Result.Err tls_codec.Error.InvalidVectorLength)
      else ok (core.result.Result.Ok (tls_serialized_len, byte_length))
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
        (Std.Usize × Std.Usize) (core.convert.From.Blanket tls_codec.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
      (Std.Usize × Std.Usize) (core.convert.From.Blanket tls_codec.Error) residual


/-- Hand-translated (not extracted):
    [tls_codec::tls_vec::{tls_codec::tls_vec::TlsByteVecU32}::get_content_lengths],
    'tls_codec/src/tls_vec.rs', lines 250:12-274:13 (macro `impl_serialize_common!`,
    instantiated by `impl_tls_byte_vec!(u32, TlsByteVecU32, 4)`, tls_vec.rs:985-988);
    aeneas cannot translate `Iterator::try_fold`.

    ```rust
                        || res.is_ok_and(|(total, content)| total == content + $len_len)))]
                $(#[$std_enabled])?
                fn get_content_lengths(&$self) -> Result<(usize, usize), Error> {
                    // Sum the element lengths with an overflow check on platforms where
                    // `usize` is narrow enough for it to matter (see `crate::len_add`).
                    // Computing `byte_length` directly (rather than deriving it from
                    // `tls_serialized_len()`) lets us reject a true overflow instead of
                    // trusting a possibly-saturated value from the `Size` impl.
                    let byte_length = $self
                        .as_slice()
                        .iter()
                        .try_fold(0usize, |acc, e| crate::checked_len_add(acc, e.tls_serialized_len()))?;
                    let tls_serialized_len = crate::checked_len_add(byte_length, $len_len)?;

                    let max_len = <$size>::MAX.try_into().unwrap();
                    #[cfg(not(hax))]
                    debug_assert!(
                        byte_length <= max_len,
                        "Vector length can't be encoded in the vector length a {} >= {}",
                        byte_length,
                        max_len
                    );
                    if byte_length > max_len {
                        return Err(Error::InvalidVectorLength);
                    }
                    Ok((tls_serialized_len, byte_length))
                }
    ```
    with `$self = self`, `$size = u32`, `$len_len = 4`.

    - `as_slice()` is inlined (its body is the one CoreModels call `deref self.vec`).
    - `try_fold` follows std (`while let Some(x) = self.next() { accum = f(accum, x)?; }
      try { accum }`): elements in order, the closure's `?` returns the first `Err`
      unchanged (`from_residual` with the identity `From`). The element method is
      `<u8 as Size>::tls_serialized_len` (`e : &u8`).
    - `u32::MAX.try_into()` is `<usize as TryFrom<u32>>` (error `TryFromIntError`), as aeneas translates `type_len.try_into().unwrap()` in `TlsByteVecU32.deserialize_bytes_bytes`.
    - `debug_assert!` is gated by `#[cfg(not(hax))]`, so it is not in the model: the
      `InvalidVectorLength` return handles `byte_length > max_len`. -/
def tls_vec.TlsByteVecU32.get_content_lengths
  (self : tls_vec.TlsByteVecU32) :
  RustM (core.result.Result (Std.Usize × Std.Usize) tls_codec.Error) := do
  let s ← alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref self.vec
  let i ← core.slice.Slice.iter s
  let r ←
    loop
      (fun (p : core.slice.iter.Iter Std.U8 × Std.Usize) => do
        let (o, iter1) ←
          core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next p.1
        match o with
        | core.option.Option.Some e =>
          let i1 ← tls_codec.Copied.U8.Insts.Tls_codecSize.tls_serialized_len e
          let r1 ← checked_len_add p.2 i1
          let cf ← core.result.Result.Insts.CoreOpsTry_traitTry.branch r1
          match cf with
          | core.ops.control_flow.ControlFlow.Continue acc1 => ok (cont (iter1, acc1))
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r2 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
                Std.Usize (core.convert.From.Blanket tls_codec.Error) residual
            ok (done r2)
        | core.option.Option.None => ok (done (core.result.Result.Ok p.2)))
      (i, 0#usize)
  let cf ← core.result.Result.Insts.CoreOpsTry_traitTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue byte_length =>
    let r1 ← checked_len_add byte_length 4#usize
    let cf1 ← core.result.Result.Insts.CoreOpsTry_traitTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue tls_serialized_len =>
      let r2 ←
        core.Usize.Insts.CoreConvertTryFromU32TryFromIntError.try_from core.num.U32.MAX
      let max_len ←
        core.result.Result.unwrap
          core.num.error.TryFromIntError.Insts.CoreFmtDebug r2
      if byte_length > max_len
      then ok (core.result.Result.Err tls_codec.Error.InvalidVectorLength)
      else ok (core.result.Result.Ok (tls_serialized_len, byte_length))
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
        (Std.Usize × Std.Usize) (core.convert.From.Blanket tls_codec.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
      (Std.Usize × Std.Usize) (core.convert.From.Blanket tls_codec.Error) residual

/-- Hand-translated (not extracted):
    [tls_codec::quic_vec::{impl tls_codec::SerializeBytes for &'_0 [T]}::tls_serialize_bytes],
    'tls_codec/src/quic_vec.rs', lines 189:4-223:5; aeneas cannot translate
    `Iterator::try_fold`.

    ```rust
    impl<T: SerializeBytes> SerializeBytes for &[T] {
        #[inline(always)]
        fn tls_serialize_bytes(&self) -> Result<Vec<u8>, Error> {
            // We need to pre-compute the length of the content.
            // This requires more computations but the other option would be to buffer
            // the entire content, which can end up requiring a lot of memory.
            let content_length = self.iter().try_fold(0usize, |acc, e| {
                crate::checked_len_add(acc, e.tls_serialized_len())
            })?;
            let length = ContentLength::from_usize(content_length)?;
            let len_len = length.0.bytes_len();

            let mut out = Vec::with_capacity(crate::checked_alloc_len(content_length, len_len)?);
            out.resize(len_len, 0);
            length.0.write_bytes(&mut out)?;

            // Serialize the elements
            let mut failure: Option<Error> = None;
            for e in self.iter() {
                match e.tls_serialize_bytes() {
                    Ok(mut bytes) => out.append(&mut bytes),
                    Err(err) => {
                        failure = Some(err);
                        break;
                    }
                }
            }
            if let Some(err) = failure {
                return Err(err);
            }
            #[cfg(debug_assertions)]
            if out.len() - len_len != content_length {
                return Err(Error::LibraryError);
            }

            Ok(out)
        }
    }
    ```

    - The `try_fold` is translated as in `get_content_lengths` above (std's
      `try_fold`, first `Err` returned unchanged); the element method is
      `<T as Size>::tls_serialized_len` (`e : &T`), i.e. `SerializeBytesInst.SizeInst`.
    - From `ContentLength::from_usize` to `write_bytes` the code is the one of
      `SerializeBytes for VLBytes` (quic_vec.rs:175-185), and so is its translation,
      copied from `quic_vec.VLBytes.Insts.Tls_codecSerializeBytes.tls_serialize_bytes`
      (`&mut out` as `deref_mut` + back function).
    - `for e in self.iter()` is `IntoIterator::into_iter(self.iter())` (the identity
      blanket impl for an iterator), then `next` until `None`. The loop state is the
      iterator and `out`; `failure` is the loop's result (`None` when the iterator is
      exhausted, `Some err` at the `break`). On `Ok(bytes)` the element bytes are
      `append`ed (CoreModels `Vec::append`; `bytes`, emptied, is dropped). Elements after
      the first failing one are not serialized.
    - `#[cfg(debug_assertions)]` is on: the `out.len() - len_len != content_length`
      check is in the model (with the panicking `-` of a debug build). -/
def Shared0Slice.Insts.Tls_codecSerializeBytes.tls_serialize_bytes
  {T : Type} (SerializeBytesInst : SerializeBytes T) (self : Slice T) :
  RustM (core.result.Result (alloc.vec.Vec Std.U8) tls_codec.Error) := do
  let i ← core.slice.Slice.iter self
  let r ←
    loop
      (fun (p : core.slice.iter.Iter T × Std.Usize) => do
        let (o, iter1) ←
          core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next p.1
        match o with
        | core.option.Option.Some e =>
          let i1 ← SerializeBytesInst.SizeInst.tls_serialized_len e
          let r1 ← checked_len_add p.2 i1
          let cf ← core.result.Result.Insts.CoreOpsTry_traitTry.branch r1
          match cf with
          | core.ops.control_flow.ControlFlow.Continue acc1 => ok (cont (iter1, acc1))
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r2 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
                Std.Usize (core.convert.From.Blanket tls_codec.Error) residual
            ok (done r2)
        | core.option.Option.None => ok (done (core.result.Result.Ok p.2)))
      (i, 0#usize)
  let cf ← core.result.Result.Insts.CoreOpsTry_traitTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue content_length =>
    let r1 ← tls_codec.Copied.quic_vec.ContentLength.from_usize content_length
    let cf1 ← core.result.Result.Insts.CoreOpsTry_traitTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let len_len ← tls_codec.Copied.varint.TlsVarInt.bytes_len val
      let r2 ← tls_codec.Copied.checked_alloc_len content_length len_len
      let cf2 ← core.result.Result.Insts.CoreOpsTry_traitTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let out ← alloc.vec.Vec.with_capacity Std.U8 val1
        let out1 ←
          alloc.vec.Vec.resize core.U8.Insts.CoreCloneClone out len_len 0#u8
        let (s1, deref_mut_back) ←
          alloc.vec.Vec.Insts.CoreOpsDerefDerefMutSlice.deref_mut out1
        let (r3, s2) ← tls_codec.Copied.varint.TlsVarInt.write_bytes val s1
        let cf3 ← core.result.Result.Insts.CoreOpsTry_traitTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let out2 := deref_mut_back s2
          let i2 ← core.slice.Slice.iter self
          let iter ←
            core.iter.traits.collect.IntoIterator.Blanket.into_iter
              (core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T) i2
          let (out3, failure) ←
            loop
              (fun (p : core.slice.iter.Iter T × alloc.vec.Vec Std.U8) => do
                let (o, iter1) ←
                  core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next p.1
                match o with
                | core.option.Option.Some e =>
                  let r4 ← SerializeBytesInst.tls_serialize_bytes e
                  match r4 with
                  | core.result.Result.Ok bytes =>
                    let (out4, _) ← alloc.vec.Vec.append p.2 bytes
                    ok (cont (iter1, out4))
                  | core.result.Result.Err err =>
                    ok (done (p.2, core.option.Option.Some err))
                | core.option.Option.None => ok (done (p.2, core.option.Option.None)))
              (iter, out2)
          match failure with
          | core.option.Option.Some err => ok (core.result.Result.Err err)
          | core.option.Option.None =>
            let i3 ← alloc.vec.Vec.len out3
            let i4 ← i3 - len_len
            if i4 != content_length
            then ok (core.result.Result.Err tls_codec.Error.LibraryError)
            else ok (core.result.Result.Ok out3)
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
            (alloc.vec.Vec Std.U8) (core.convert.From.Blanket tls_codec.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.From.Blanket tls_codec.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
        (alloc.vec.Vec Std.U8) (core.convert.From.Blanket tls_codec.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.From.Blanket tls_codec.Error) residual

/-- Hand-translated (not extracted):
    [tls_codec::primitives::{impl tls_codec::DeserializeBytes for alloc::boxed::Box<T>}::tls_deserialize_bytes],
    'tls_codec/src/primitives.rs', lines 441:4-443:5; aeneas fails on the `map`
    closure ("Can't end abstraction").

    ```rust
    impl<T: DeserializeBytes> DeserializeBytes for Box<T> {
        #[inline(always)]
        fn tls_deserialize_bytes(bytes: &[u8]) -> Result<(Self, &[u8]), Error> {
            T::tls_deserialize_bytes(bytes).map(|(v, r)| (Box::new(v), r))
        }
    }
    ```

    `Box` is erased by aeneas (`--treat-box-as-builtin`, `Box<T>` is `T`), so
    `Box::new` is the identity and the closure `|(v, r)| (Box::new(v), r)` is the
    identity on pairs; `Result::map` of it is written out as a `match` (the closure has
    no extracted `FnOnce` instance to pass to CoreModels' `Result::map`). -/
def Box.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes
  {T : Type} (DeserializeBytesInst : DeserializeBytes T) (bytes : Slice Std.U8) :
  RustM (core.result.Result (T × (Slice Std.U8)) tls_codec.Error) := do
  let r ← DeserializeBytesInst.tls_deserialize_bytes bytes
  match r with
  | core.result.Result.Ok (v, r1) => ok (core.result.Result.Ok (v, r1))
  | core.result.Result.Err e => ok (core.result.Result.Err e)

end -- noncomputable section
