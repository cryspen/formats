/- Missing core models: `core` / `alloc` items the extraction references that
CoreModels (hax-lean v0.3.27) does not provide. Crate-independent (imports only
Aeneas and CoreModels), so `-extra-includes` can import it into every generated file.
Specs for these and for existing CoreModels functions: `MissingCoreModelsSpecs.lean`. -/
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

/-! ## Hand-written stopgaps for CoreModels gaps (not generated)

Rust `core`/`alloc` items that Extraction/Funs.lean references but that
CoreModels (hax-lean v0.3.27) does not provide. Candidates for upstreaming into
hax's core models. Where the Rust semantics is trivial and certain, the item is
a `def` that follows the Rust implementation; otherwise it is an opaque `axiom`
that only fixes the type. -/

/-- [alloc::string::{impl core::cmp::PartialEq<String> for String}::eq] -/
def alloc.string.String.Insts.CoreCmpPartialEqString.eq
  (self other : alloc.string.String) : RustM Bool :=
  ok (@decide (self = other) (instDecidableEqString self other))

/-- [alloc::string::{impl core::clone::Clone for String}::clone] -/
def alloc.string.String.Insts.CoreCloneClone.clone
  (self : alloc.string.String) : RustM alloc.string.String :=
  ok self

/-- [alloc::string::{impl core::convert::From<&str> for String}::from]: the
    string whose UTF-8 encoding is the bytes of `s` (aeneas' `Str` is
    `Slice U8`). Rust's `&str` is always valid UTF-8 (building one that is not
    is undefined behaviour), so the `undef` branch has no Rust counterpart;
    `toStr "…"` literals always take the first branch. -/
def alloc.string.String.Insts.CoreConvertFromShared0Str.from
  (s : Str) : RustM alloc.string.String :=
  match String.fromUTF8? ⟨(s.val.map fun b : Std.U8 => UInt8.ofBitVec b.bv).toArray⟩ with
  | some t => ok t
  | none => fail .undef

/-- [alloc::string::{impl core::convert::From<&str> for String}] -/
@[reducible]
def alloc.string.String.Insts.CoreConvertFromShared0Str :
  core.convert.From alloc.string.String Str := {
  «from» := alloc.string.String.Insts.CoreConvertFromShared0Str.from
}

/-- [alloc::string::{String}::from_utf8]: `Ok` with the string whose UTF-8
    encoding is `vec` iff `vec` is well-formed UTF-8, else `Err` carrying `vec`.
    `ByteArray.IsValidUTF8 b` is `∃ cs : List Char, b = cs.utf8Encode` (Lean
    `Char`s are Unicode scalar values, the encoding is the shortest form), which
    is Unicode's well-formed UTF-8 and so Rust's check (no overlong forms, no
    surrogates, nothing above U+10FFFF, no truncated sequence). -/
def alloc.string.String.from_utf8 (vec : alloc.vec.Vec Std.U8) :
  RustM (core.result.Result alloc.string.String alloc.string.FromUtf8Error) :=
  match String.fromUTF8? ⟨(vec.val.map fun b : Std.U8 => UInt8.ofBitVec b.bv).toArray⟩ with
  | some s => ok (core.result.Result.Ok s)
  | none => ok (core.result.Result.Err { bytes := vec })

/-- [alloc::string::{String}::as_bytes]: the UTF-8 encoding of `self`.
    A Rust `String` has at most `isize::MAX` bytes, so the bytes always fit a
    slice. CoreModels' `alloc.string.String` is Lean's unbounded `String`: a model
    string longer than `usize::MAX` bytes has no Rust counterpart, and gets its
    longest prefix that fits (keeping `as_bytes` total, as in Rust). -/
def alloc.string.String.as_bytes (self : alloc.string.String) : RustM (Slice Std.U8) :=
  let l := self.toByteArray.data.toList.map fun b : UInt8 => (⟨b.toBitVec⟩ : Std.U8)
  ok ⟨l.take Usize.max, by simp⟩

namespace CoreModels

/-- [alloc::string::{impl core::fmt::Display for FromUtf8Error}::fmt] -/
axiom alloc.string.FromUtf8Error.Insts.CoreFmtDisplay.fmt :
  alloc.string.FromUtf8Error → core.fmt.Formatter →
  RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [alloc::string::{impl core::fmt::Display for FromUtf8Error}] -/
@[reducible]
noncomputable def alloc.string.FromUtf8Error.Insts.CoreFmtDisplay :
  core.fmt.Display alloc.string.FromUtf8Error := {
  fmt := alloc.string.FromUtf8Error.Insts.CoreFmtDisplay.fmt
}

/-- [core::num::error::{impl core::fmt::Debug for TryFromIntError}::fmt] -/
axiom core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt :
  core.num.error.TryFromIntError → core.fmt.Formatter →
  RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [core::num::error::{impl core::fmt::Debug for TryFromIntError}] -/
@[reducible]
noncomputable def core.num.error.TryFromIntError.Insts.CoreFmtDebug :
  core.fmt.Debug core.num.error.TryFromIntError := {
  fmt := core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt
}

/-- [core::convert::{impl core::fmt::Debug for Infallible}::fmt] -/
axiom core.convert.Infallible.Insts.CoreFmtDebug.fmt :
  core.convert.Infallible → core.fmt.Formatter →
  RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [core::convert::{impl core::fmt::Debug for Infallible}] -/
@[reducible]
noncomputable def core.convert.Infallible.Insts.CoreFmtDebug :
  core.fmt.Debug core.convert.Infallible := {
  fmt := core.convert.Infallible.Insts.CoreFmtDebug.fmt
}

/-- [core::convert::{impl core::convert::TryFrom<U> for T}::try_from]
    (`where U: Into<T>`, `type Error = Infallible`): `Ok(U::into(value))`, as in
    Rust's `core`. CoreModels has this blanket impl as
    `convert.TryFromUTInfallible.Blanket` with a `From` bound instead. -/
def core.convert.TryFromTUInfallible.Blanket.try_from
  {T U : Type} (IntoInst : core.convert.Into U T) (value : U) :
  RustM (core.result.Result T core.convert.Infallible) := do
  let t ← IntoInst.into value
  ok (core.result.Result.Ok t)

/-- [core::mem::take]: `replace(dest, T::default())`, returning
    `(old value, new *dest)` as aeneas encodes `&mut` arguments. -/
def core.mem.take
  {T : Type} (DefaultInst : core.default.Default T) (dest : T) :
  RustM (T × T) := do
  let d ← DefaultInst.default
  ok (dest, d)

/-- [core::mem::size_of]. A type-directed constant, so it cannot be defined over
    an arbitrary `Type`: opaque, with its value fixed below for the types this
    crate queries (`primitives.rs:162`, `lib.rs:412`, `lib.rs:429`). -/
axiom core.mem.size_of (T : Type) : RustM Std.Usize

axiom core.mem.size_of_U8 : core.mem.size_of Std.U8 = ok 1#usize
axiom core.mem.size_of_U16 : core.mem.size_of Std.U16 = ok 2#usize
axiom core.mem.size_of_U32 : core.mem.size_of Std.U32 = ok 4#usize
axiom core.mem.size_of_U64 : core.mem.size_of Std.U64 = ok 8#usize

/-- `usize` is as wide as a pointer, which aeneas models by
    `System.Platform.numBits`. -/
axiom core.mem.size_of_Usize :
  ∃ n : Std.Usize, core.mem.size_of Std.Usize = ok n ∧ n.val * 8 = System.Platform.numBits

/-- [alloc::boxed::{impl core::convert::AsRef<T> for Box<T>}::as_ref]
    (`Box` is erased by aeneas, so this is the identity). -/
def alloc.Box.Insts.CoreConvertAsRef.as_ref {T : Type} (self : T) : RustM T :=
  ok self

/-- [core::fmt::{Arguments}::from_str]. `core.fmt.Arguments` is `Unit` in
    CoreModels. -/
def core.fmt.Arguments.from_str (_s : Str) : RustM core.fmt.Arguments :=
  ok ()

/-- [core::fmt::rt::{Argument}::new_display] -/
axiom core.fmt.rt.Argument.new_display
  {T : Type} (DisplayInst : core.fmt.Display T) :
  T → RustM core.fmt.rt.Argument

/-- [alloc::fmt::format] -/
axiom alloc.fmt.format : core.fmt.Arguments → RustM alloc.string.String

/-- [alloc::vec::{impl core::iter::traits::collect::Extend<&'a T> for Vec<T>}::extend]:
    `self.spec_extend(iter.into_iter())`, i.e. push a copy of each item, in
    iteration order, until `next` returns `None`. aeneas erases the `&T` (items
    are `T`), and a `Copy` copy is bitwise (no `Clone::clone` call), so `CopyInst`
    is unused. Running out of length bound fails as `Vec::push` does (std panics
    with "capacity overflow"). A non-terminating iterator makes `loop` diverge. -/
def alloc.vec.Vec.Insts.CoreIterTraitsCollectExtendSharedAT.extend
  {T I IntoIter : Type} (CopyInst : core.marker.Copy T)
  (IntoIteratorInst : core.iter.traits.collect.IntoIterator I T IntoIter)
  (self : alloc.vec.Vec T) (iter : I) : RustM (alloc.vec.Vec T) := do
  let it ← IntoIteratorInst.into_iter iter
  loop (fun (p : IntoIter × alloc.vec.Vec T) => do
      let (o, it1) ← IntoIteratorInst.iteratorIteratorInst.next p.1
      match o with
      | core.option.Option.Some x =>
        let v ← alloc.vec.Vec.push p.2 x
        ok (cont (it1, v))
      | core.option.Option.None => ok (done p.2))
    (it, self)

/-- [alloc::vec::{impl core::hash::Hash for Vec<T>}::hash] -/
axiom alloc.vec.Vec.Insts.CoreHashHash.hash
  {T H : Type} (HashInst : core.hash.Hash T) (HasherInst : core.hash.Hasher H) :
  alloc.vec.Vec T → H → RustM H

/-- [alloc::vec::{impl core::cmp::Ord for Vec<T>}::cmp] -/
axiom alloc.vec.Vec.Insts.CoreCmpOrd.cmp
  {T : Type} (OrdInst : core.cmp.Ord T) :
  alloc.vec.Vec T → alloc.vec.Vec T → RustM core.cmp.Ordering

/-- [alloc::vec::{Vec<T>}::retain] -/
axiom alloc.vec.Vec.retain
  {T F : Type} (FnMutInst : core.ops.function.FnMut F T Bool) :
  alloc.vec.Vec T → F → RustM (alloc.vec.Vec T)

end CoreModels


/-! ## `Lawful` structures of core traits (trait-level specs, aeneas `818b3fa6`)

The generated specs and per-impl obligations refer to `Trait.Lawful` for every
trait an impl or a bound mentions, including core traits, which CoreModels does
not provide yet. A field is a proof obligation of each impl's `Lawful` theorem,
never an axiom, so these structures assume nothing about arbitrary impls; a
generic spec gets them as `…InstLawful` hypotheses.

Fields (2026-10-15), each the contract Rust documents for the trait:
- no failure (panic or divergence): `Clone.clone`, `PartialEq.eq` / `ne`,
  `From.from` ("must not fail"), `TryFrom.try_from` (failure is an `Err`),
  `Default.default`, `Borrow.borrow`, `AsRef.as_ref`;
- `Eq`: the parent `eq` decides `=` (the model's equality is structural).
No field, on purpose:
- `Index` / `IndexMut`: the bound (`i < len`) depends on `Idx` and the impl, so it
  stays an impl-level (standalone) spec;
- `PartialOrd` / `Ord` (CoreModels' `Vec` `cmp` is an axiom), `Hash` (stub
  `Hasher`), `Debug` / `Display` (the `fmt` exclusion is open), `Drop` (stub
  `zeroize`), `FnOnce` / `FnMut` (closures may fail), `FromIterator`, and the
  markers `Copy`, `StructuralPartialEq`, `Error`. -/

namespace CoreModels

/-- `clone_spec`: `clone` does not fail (no panic, no divergence); the result is
    unconstrained. Needed by generic callers of `clone` that must prove a `⇓`
    (total-correctness) post, e.g. `from_slice` (`Slice::to_vec`). -/
structure core.clone.Clone.Lawful (Self : Type) (CloneInst : core.clone.Clone Self) : Prop where
  clone_spec (x : Self) : ⦃ ⌜ True ⌝ ⦄ CloneInst.clone x ⦃ ⇓ _ => ⌜ True ⌝ ⦄

structure core.borrow.Borrow.Lawful (Self : Type) (Borrowed : Type)
  (BorrowInst : core.borrow.Borrow Self Borrowed) : Prop where
  borrow_spec (x : Self) : ⦃ ⌜ True ⌝ ⦄ BorrowInst.borrow x ⦃ ⇓ _ => ⌜ True ⌝ ⦄

/-- `eq_spec`: the parent `PartialEq::eq` decides `=`. -/
structure core.cmp.Eq.Lawful (Self : Type)
  (EqInst : core.cmp.Eq Self) : Prop where
  eq_spec (x y : Self) :
    ⦃ ⌜ True ⌝ ⦄ EqInst.PartialEqInst.eq x y ⦃ ⇓ r => ⌜ r = true ↔ x = y ⌝ ⦄

structure core.cmp.Ord.Lawful (Self : Type)
  (OrdInst : core.cmp.Ord Self) : Prop where

structure core.cmp.PartialEq.Lawful (Self : Type) (Rhs : Type)
  (PartialEqInst : core.cmp.PartialEq Self Rhs) : Prop where
  eq_spec (x : Self) (y : Rhs) : ⦃ ⌜ True ⌝ ⦄ PartialEqInst.eq x y ⦃ ⇓ _ => ⌜ True ⌝ ⦄
  ne_spec (x : Self) (y : Rhs) : ⦃ ⌜ True ⌝ ⦄ PartialEqInst.ne x y ⦃ ⇓ _ => ⌜ True ⌝ ⦄

structure core.cmp.PartialOrd.Lawful (Self : Type) (Rhs : Type)
  (PartialOrdInst : core.cmp.PartialOrd Self Rhs) : Prop where

structure core.convert.AsRef.Lawful (Self : Type) (T : Type)
  (AsRefInst : core.convert.AsRef Self T) : Prop where
  as_ref_spec (x : Self) : ⦃ ⌜ True ⌝ ⦄ AsRefInst.as_ref x ⦃ ⇓ _ => ⌜ True ⌝ ⦄

structure core.convert.From.Lawful (Self : Type) (T : Type)
  (FromInst : core.convert.From Self T) : Prop where
  from_spec (x : T) : ⦃ ⌜ True ⌝ ⦄ FromInst.«from» x ⦃ ⇓ _ => ⌜ True ⌝ ⦄

structure core.convert.TryFrom.Lawful (Self : Type) (T : Type) (Self_Error : Type)
  (TryFromInst : core.convert.TryFrom Self T Self_Error) : Prop where
  try_from_spec (x : T) : ⦃ ⌜ True ⌝ ⦄ TryFromInst.try_from x ⦃ ⇓ _ => ⌜ True ⌝ ⦄

structure core.default.Default.Lawful (Self : Type)
  (DefaultInst : core.default.Default Self) : Prop where
  default_spec : ⦃ ⌜ True ⌝ ⦄ DefaultInst.default ⦃ ⇓ _ => ⌜ True ⌝ ⦄

structure core.error.Error.Lawful (Self : Type)
  (ErrorInst : core.error.Error Self) : Prop where

structure core.fmt.Debug.Lawful (Self : Type)
  (DebugInst : core.fmt.Debug Self) : Prop where

structure core.fmt.Display.Lawful (Self : Type)
  (DisplayInst : core.fmt.Display Self) : Prop where

structure core.hash.Hash.Lawful (Self : Type)
  (HashInst : core.hash.Hash Self) : Prop where

structure core.iter.traits.collect.FromIterator.Lawful (Self : Type) (A : Type)
  (FromIteratorInst : core.iter.traits.collect.FromIterator Self A) : Prop where

structure core.marker.Copy.Lawful (Self : Type)
  (CopyInst : core.marker.Copy Self) : Prop where

structure core.marker.StructuralPartialEq.Lawful (Self : Type)
  (StructuralPartialEqInst : core.marker.StructuralPartialEq Self) : Prop where

structure core.ops.drop.Drop.Lawful (Self : Type)
  (DropInst : core.ops.drop.Drop Self) : Prop where

structure core.ops.function.FnMut.Lawful (Self : Type) (Args : Type) (Self_Output : Type)
  (FnMutInst : core.ops.function.FnMut Self Args Self_Output) : Prop where

structure core.ops.function.FnOnce.Lawful (Self : Type) (Args : Type) (Self_Output : Type)
  (FnOnceInst : core.ops.function.FnOnce Self Args Self_Output) : Prop where

structure core.ops.index.Index.Lawful (Self : Type) (Idx : Type) (Self_Output : Type)
  (IndexInst : core.ops.index.Index Self Idx Self_Output) : Prop where

structure core.ops.index.IndexMut.Lawful (Self : Type) (Idx : Type) (Self_Output : Type)
  (IndexMutInst : core.ops.index.IndexMut Self Idx Self_Output) : Prop where

end CoreModels
