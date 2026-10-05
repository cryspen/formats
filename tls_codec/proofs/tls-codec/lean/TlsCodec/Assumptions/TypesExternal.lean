-- [tls_codec]: external types.
-- Seeded by hax from Extraction/TypesExternal_Template.lean: fill the holes.
-- hax never modifies this file; after re-extraction, compare it against the
-- regenerated template to see what changed.
import Aeneas
import CoreModels
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


/-! Hand-written model (not generated): the third-party trait `zeroize::Zeroize`
    (zeroize 1.9, `pub trait Zeroize { fn zeroize(&mut self); }`).
    Encoded the way aeneas encodes traits: a structure with one field per
    method; the `&mut self` method returning `()` becomes `Self → RustM Self`
    (same shape as aeneas' `core.ops.drop.Drop`). -/
structure zeroize.Zeroize (Self : Type) where
  zeroize : Self → RustM Self

/-- Hand-written stopgap (not generated): `alloc::string::FromUtf8Error` is
    referenced by Extraction/Funs.lean but not provided by CoreModels
    (hax-lean v0.3.27).

    Rust: `struct FromUtf8Error { bytes: Vec<u8>, error: Utf8Error }`, private
    fields, built only by `String::from_utf8` from the rejected input. `error`
    (`valid_up_to`, `error_len`) is computed from `bytes` by std's validator, so
    it carries no further information and is left out: `bytes` determines the
    Rust value. -/
structure CoreModels.alloc.string.FromUtf8Error : Type where
  /-- The rejected input (`FromUtf8Error::into_bytes`). -/
  bytes : alloc.vec.Vec Std.U8
