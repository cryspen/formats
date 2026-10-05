/- Shared helpers for the proofs in `PanicFreedom.lean` / `FunctionalCorrectness.lean`. -/
import Aeneas
import CoreModels
import Hax
import TlsCodec.Extraction
import TlsCodec.Verification.MissingSpecs
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option mvcgen.warning false
set_option hax_mvcgen.warnings false

namespace tls_codec

/-! ### `pre.holds` hypotheses

No helper is needed: `hax_mvcgen [f, <crate defs called by the pre>]` introduces the
`(f.pre …).holds` hypothesis, runs `mvcgen` on it (hax's `hax_mvcgen at`) with the registered
`@[spec]` lemmas, and then runs `mvcgen` on the goal. -/

/-! ### `?` on `Result`

`x?` is extracted as `let cf ← branch x; match cf with | Continue v => … | Break res =>
from_residual T FromInst res`. `branch_tryCF_spec` states the result of `branch` as
`cf = tryCF x`, a plain def instead of a `match` (a `match` in a spec post is an anonymous
matcher, which no rewrite lemma can target). `mvcgen` then leaves, per `?`:
- in the `Continue v` branch, a hypothesis `Continue v = tryCF x`; `continue_eq_tryCF`
  turns it into `x = .Ok v` when a proof needs the callee's result (`simp only
  [continue_eq_tryCF] at *`);
- in the `Break res` branch, the hypothesis of the (global) `from_residual_spec`, as the VC
  `Break res = tryCF x → ∃ e, res = .Err e ∧ ⦃⌜True⌝⦄ FromInst.from e ⦃…⦄`, which `try_vcs`
  closes. -/

/-- The control flow of `x?`. -/
def tryCF {T E : Type} : core.result.Result T E →
    core.ops.control_flow.ControlFlow (core.result.Result core.convert.Infallible E) T
  | .Ok v => .Continue v
  | .Err e => .Break (.Err e)

/-- `branch`, with the result as `tryCF x`. `high`: wins over MissingSpecs' `branch_spec`. -/
@[spec high] theorem branch_tryCF_spec {T E : Type} (x : core.result.Result T E) :
    ⦃ ⌜ True ⌝ ⦄ core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch x
    ⦃ ⇓ r => ⌜ r = tryCF x ⌝ ⦄ := by
  mvcgen [CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch_spec]

theorem continue_eq_tryCF {T E : Type} {x : core.result.Result T E} {v : T} :
    (.Continue v = tryCF x) ↔ x = .Ok v := by
  cases x <;> simp [tryCF, eq_comm]

/-- The `Break` VC of `x?`: the residual is `Err e`, with `x = Err e`. -/
theorem try_break_vc {T E : Type} {x : core.result.Result T E}
    {res : core.result.Result core.convert.Infallible E} {P : E → Prop}
    (h : ∀ e, x = .Err e → P e) :
    .Break res = tryCF x → ∃ e, res = .Err e ∧ P e := by
  cases x <;> simp_all [tryCF]

/-- Close the `Break` VCs of `?` (see above). Other goals are left untouched: `apply
try_break_vc` fails at once on them. The optional list goes to the `mvcgen` that proves
the `From` triple: crate `From` impls to unfold, e.g.
`try_vcs [Error.Insts.CoreConvertFromTryFromIntError.from]`. The identity `From` needs nothing
(`From.Blanket.from_spec` is global). -/
syntax "try_vcs" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| try_vcs) => `(tactic| try_vcs [])
  | `(tactic| try_vcs [$ts,*]) =>
    `(tactic| all_goals (first | (apply try_break_vc; intros; mvcgen [$ts,*]) | skip))

/-! ### Scalar casts -/

/-- `usize as u64` is lossless (`usize` is at most 64 bits wide). -/
@[simp, scalar_tac_simps] theorem Usize.cast_U64_val_eq (x : Std.Usize) :
    (UScalar.cast .U64 x).val = x.val := by
  have := x.hBounds
  rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalar.cast_val_eq] <;> omega

/-- Value of a saturating add: capped at the type's maximum. -/
@[simp, scalar_tac_simps] theorem UScalar.saturating_add_val {ty : UScalarTy} (x y : UScalar ty) :
    (UScalar.saturating_add x y).val = min (UScalar.max ty) (x.val + y.val) := by
  have hmax : UScalar.max ty < 2 ^ ty.numBits := by
    simp only [UScalar.max]; have := Nat.two_pow_pos ty.numBits; omega
  have hlt : min (UScalar.max ty) (x.val + y.val) < 2 ^ ty.numBits :=
    Nat.lt_of_le_of_lt (Nat.min_le_left _ _) hmax
  simp only [UScalar.saturating_add, UScalar.val, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hlt

/-- Small numbers are not reduced modulo `Usize.size` (which is `2^32` or `2^64`). -/
@[simp, scalar_tac_simps] theorem Usize.mod_size_of_lt (n : Nat) (h : n < 2 ^ 32) :
    n % Usize.size = n := by
  apply Nat.mod_eq_of_lt
  rw [Usize.size_scalarTac_eq.2]
  rcases System.Platform.numBits_eq with h' | h' <;> rw [h'] <;> omega

/-- `isize::MAX as usize` is half of `usize::MAX` (rounded down): stated linearly for `omega`. -/
theorem Usize.hcast_Isize_MAX_val :
    (IScalar.hcast UScalarTy.Usize core.num.Isize.MAX).val * 2 + 1 = UScalar.max UScalarTy.Usize := by
  rw [IScalar.hcast_val_eq]
  have hM : (core.num.Isize.MAX).val = Isize.max := by simp [core.num.Isize.MAX]
  rw [hM]
  rcases System.Platform.numBits_eq with h | h <;>
    simp [Isize.max, UScalar.max, UScalarTy.numBits, Isize.numBits, IScalarTy.numBits, h]

/-! ### Indexing with a `usize`

`v[i]` goes through the generic `Index` specs of MissingSpecs, whose hypothesis is stated on
`get` (`∃ r, o = some r ∧ …`) and is not closed by `scalar_tac`. These direct specs have the
bound as their only hypothesis, so the VC is `i < len`. `high`: they must win over the generic ones. -/

/-- `v[i]` on a `Vec`, `i : usize` in bounds. -/
@[spec high] theorem alloc.vec.Vec.index_usize_spec {T : Type} (v : alloc.vec.Vec T) (i : Std.Usize)
    (h : i.val < v.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    alloc.vec.Vec.Insts.CoreOpsIndexIndex.index (core.Usize.Insts.CoreSliceIndexSliceIndexSliceT T) v i
    ⦃ ⇓ r => ⌜ r = v.val[i.val] ⌝ ⦄ := by
  apply CoreModels.alloc.vec.Vec.Insts.CoreOpsIndexIndex.index_spec
  mvcgen
  simp_all [PostCond.ok]

/-- `s[i]` on a slice, `i : usize` in bounds. -/
@[spec high] theorem core.Slice.index_usize_spec {T : Type} (s : Slice T) (i : Std.Usize)
    (h : i.val < s.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    core.Slice.Insts.CoreOpsIndexIndex.index (core.Usize.Insts.CoreSliceIndexSliceIndexSliceT T) s i
    ⦃ ⇓ r => ⌜ r = s.val[i.val] ⌝ ⦄ := by
  apply CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index_spec
  mvcgen
  simp_all [PostCond.ok]

/-! ### Specs of small shared functions -/

/-- `bytes_len` returns a length in `1..=8`, determined by the value (so two calls on the same
value agree). -/
@[spec] theorem varint.TlsVarInt.bytes_len_spec (self : varint.TlsVarInt) :
    ⦃ ⌜ True ⌝ ⦄ varint.TlsVarInt.bytes_len self
    ⦃ ⇓ r => ⌜ 1 ≤ r.val ∧ r.val ≤ 8 ∧
               (self.val ≤ 63 → r.val = 1) ∧
               (63 < self.val → self.val ≤ 16383 → r.val = 2) ∧
               (16383 < self.val → self.val ≤ 1073741823 → r.val = 4) ∧
               (1073741823 < self.val → r.val = 8) ⌝ ⦄ := by
  mvcgen [varint.TlsVarInt.bytes_len] <;> scalar_tac

/-- `MAX_MLS_LEN` is `2^30 - 1`. -/
@[spec] theorem quic_vec.MAX_MLS_LEN_spec :
    ⦃ ⌜ True ⌝ ⦄ quic_vec.MAX_MLS_LEN ⦃ ⇓ r => ⌜ r.val = 2 ^ 30 - 1 ⌝ ⦄ := by
  mvcgen [quic_vec.MAX_MLS_LEN] <;> scalar_tac

/-- `TlsVarInt::MAX` is `2^62 - 1`. -/
@[spec] theorem varint.TlsVarInt.MAX_spec :
    ⦃ ⌜ True ⌝ ⦄ varint.TlsVarInt.MAX ⦃ ⇓ r => ⌜ r.val = 2 ^ 62 - 1 ⌝ ⦄ := by
  mvcgen [varint.TlsVarInt.MAX] <;> scalar_tac

/-- `try_new` does not panic; it succeeds, returning its argument, iff the argument is at most `MAX`. -/
@[spec] theorem varint.TlsVarInt.try_new_spec (value : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄ varint.TlsVarInt.try_new value
    ⦃ ⇓ r => ⌜ match r with
                | .Ok v => v = value ∧ value.val ≤ 2 ^ 62 - 1
                | .Err e => e = Error.InvalidVectorLength ∧ 2 ^ 62 - 1 < value.val ⌝ ⦄ := by
  mvcgen [varint.TlsVarInt.try_new]
  all_goals exact ⟨trivial, by scalar_tac⟩

/-- `ContentLength::from_usize` does not panic; it succeeds, returning the value, iff the value is
below `2^30`. -/
@[spec] theorem quic_vec.ContentLength.from_usize_spec (value : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ quic_vec.ContentLength.from_usize value
    ⦃ ⇓ r => ⌜ match r with
                | .Ok c => c.val = value.val ∧ value.val ≤ 2 ^ 30 - 1
                | .Err _ => 2 ^ 30 - 1 < value.val ⌝ ⦄ := by
  mvcgen [quic_vec.ContentLength.from_usize, quic_vec.ContentLength.new,
    quic_vec.ContentLength.MAX, quic_vec.MAX_MLS_LEN_spec, varint.TlsVarInt.value,
    varint.TlsVarInt.MAX_spec]
  try_vcs [Error.Insts.CoreConvertFromTryFromIntError.from]
  · -- `new` fails: the value is above `MAX_MLS_LEN`
    rename_i _ h5 _ _ _ h4 r2 _ _ _ _ h2 _ _ _
    rw [continue_eq_tryCF] at h4 h2
    subst h5 h2
    simp only [core.result.Result.Ok.injEq] at h4
    subst h4
    scalar_tac
  · -- the `Ok` path: `value` went through `try_from` and `try_new` unchanged
    rename_i _ h5 _ _ _ h4 r2 h3 _ _ _ h2 _ _ _
    rw [continue_eq_tryCF] at h4 h2
    subst h5 h2
    simp only [core.result.Result.Ok.injEq] at h4
    subst h4
    obtain ⟨hv, _⟩ := h3
    subst hv
    scalar_tac
  · -- `try_new` fails: the value is above `2^62 - 1`
    rename_i _ h5 _ _ _ h4 _ h3 _ _ _ _ a _
    rw [continue_eq_tryCF] at h4
    subst h5 a
    simp only [core.result.Result.Ok.injEq] at h4
    subst h4
    obtain ⟨_, hb⟩ := h3
    intro _
    simp only [PostCond.ok]
    show 2 ^ 30 - 1 < value.val
    scalar_tac
  · -- `try_from` does not fail
    rename_i _ h _ _ _ _ a
    subst h
    cases a

/-- `to_vec` on a `u8` slice does not panic and returns a copy (`u8::clone` is the identity). -/
@[spec] theorem alloc.slice.Slice.to_vec_U8_spec (s : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ alloc.slice.Slice.to_vec core.U8.Insts.CoreCloneClone s
    ⦃ ⇓ r => ⌜ (r : Slice Std.U8) = s ⌝ ⦄ :=
  CoreModels.alloc.slice.Slice.to_vec_spec _ s CoreModels.core.U8.Insts.CoreCloneClone.clone_spec

/-- Number of bytes of the varint encoding of `v`. -/
def varint.lenOf (v : Nat) : Nat :=
  if v ≤ 63 then 1 else if v ≤ 16383 then 2 else if v ≤ 1073741823 then 4 else 8

/-- The facts of `bytes_len_spec` determine the length: `lenOf`, one of `1, 2, 4, 8`. -/
theorem varint.lenOf_char (self : Std.U64) (r : Std.Usize)
    (h : 1 ≤ r.val ∧ r.val ≤ 8 ∧ (self.val ≤ 63 → r.val = 1) ∧
      (63 < self.val → self.val ≤ 16383 → r.val = 2) ∧
      (16383 < self.val → self.val ≤ 1073741823 → r.val = 4) ∧
      (1073741823 < self.val → r.val = 8)) :
    r.val = varint.lenOf self.val ∧ (r.val = 1 ∨ r.val = 2 ∨ r.val = 4 ∨ r.val = 8) := by
  unfold varint.lenOf
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  split_ifs <;> omega

/-- The closure of `quic_vec::tls_serialize_bytes_len` returns a length in `1..=8`, namely `lenOf`. -/
@[spec] theorem quic_vec.tls_serialize_bytes_len.closure_call_once_spec
    (c : quic_vec.tls_serialize_bytes_len.closure) (a : quic_vec.ContentLength) :
    ⦃ ⌜ True ⌝ ⦄
    quic_vec.tls_serialize_bytes_len.closure.Insts.CoreOpsFunctionFnOnceTupleContentLengthUsize.call_once c a
    ⦃ ⇓ r => ⌜ 1 ≤ r.val ∧ r.val ≤ 8 ∧ r.val = varint.lenOf a.val ⌝ ⦄ := by
  mvcgen [quic_vec.tls_serialize_bytes_len.closure.Insts.CoreOpsFunctionFnOnceTupleContentLengthUsize.call_once]
  intro h1 h2 h3 h4 h5 h6
  exact ⟨h1, h2, (varint.lenOf_char _ _ ⟨h1, h2, h3, h4, h5, h6⟩).1⟩

/-- `Result::map` with the closure of `quic_vec::tls_serialize_bytes_len` and a plain
(non-schematic) post: an `Ok` input is mapped to an `Ok` length in `1..=8`, an `Err` is passed
through. (Specialised: a generic `P` is not inferred by `mvcgen`.) -/
@[spec] theorem quic_vec.tls_serialize_bytes_len.closure_map_spec
    (x : core.result.Result quic_vec.ContentLength Error) :
    ⦃ ⌜ True ⌝ ⦄
    core.result.Result.map
      quic_vec.tls_serialize_bytes_len.closure.Insts.CoreOpsFunctionFnOnceTupleContentLengthUsize x ()
    ⦃ ⇓ r => ⌜ (∀ t, x = .Ok t → ∃ u, r = .Ok u ∧ 1 ≤ u.val ∧ u.val ≤ 8 ∧ u.val = varint.lenOf t.val) ∧
               (∀ e, x = .Err e → r = .Err e) ⌝ ⦄ := by
  apply CoreModels.core.result.Result.map_spec
  · intro t ht; mvcgen [quic_vec.tls_serialize_bytes_len.closure_call_once_spec]
    intro h1 h2 h3
    subst ht
    refine ⟨fun t' h => ?_, fun e h => ?_⟩
    · obtain rfl := core.result.Result.Ok.inj h
      exact ⟨_, rfl, h1, h2, h3⟩
    · cases h
  · intro e he; subst he; simp [PostCond.ok]

/-- `Result::unwrap_or`, with the post stated as one implication per constructor. -/
@[spec] theorem core.result.Result.unwrap_or_cases_spec {T E : Type} (x : core.result.Result T E)
    (d : T) : ⦃ ⌜ True ⌝ ⦄ core.result.Result.unwrap_or x d
    ⦃ ⇓ r => ⌜ (∀ t, x = .Ok t → r = t) ∧ (∀ e, x = .Err e → r = d) ⌝ ⦄ := by
  mvcgen [CoreModels.core.result.Result.unwrap_or_spec]
  cases x <;> simp_all

/-- The error-mapping closure of `[u8; LEN]::tls_deserialize_bytes` does not panic. -/
@[spec] theorem arrays.DeserializeBytesArrayU8LEN.tls_deserialize_bytes.closure_call_once_spec
    {LEN : Std.Usize} (c : arrays.DeserializeBytesArrayU8LEN.tls_deserialize_bytes.closure LEN)
    (e : core.array.TryFromSliceError) :
    ⦃ ⌜ True ⌝ ⦄
    arrays.DeserializeBytesArrayU8LEN.tls_deserialize_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorError.call_once
      c e
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  mvcgen [arrays.DeserializeBytesArrayU8LEN.tls_deserialize_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorError.call_once]

/-- `[u8; LEN]::tls_deserialize_bytes` does not panic; on success it consumes exactly `LEN` bytes. -/
@[spec] theorem ArrayU8LEN.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes_spec
    (LEN : Std.Usize) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ ArrayU8LEN.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes LEN bytes
    ⦃ ⇓ r => ⌜ ∀ v rem, r = .Ok (v, rem) → rem.val.length + LEN.val = bytes.val.length ⌝ ⦄ := by
  mvcgen [ArrayU8LEN.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes,
    core.option.Option.ok_or_spec, core.result.Result.map_err_spec]
  try_vcs
  · simp only [continue_eq_tryCF] at *
    have hle : LEN.val ≤ bytes.val.length := by grind [tryCF]
    intro h _
    obtain ⟨t, ht, hlen⟩ := h hle
    refine ⟨t, ht, ?_⟩
    mvcgen
    intro _ _ h
    simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at h
    have hl := congrArg List.length hlen
    simp only [List.length_drop] at hl
    scalar_tac
  · simp only [PostCond.ok]
    mvcgen
    try_vcs
    intros
    simp [PostCond.ok]
  · simp [PostCond.ok]


/-! ### `len` of the vector wrappers (FC round 1) -/

/-- `TlsVecU8::len` is the length of the inner vector. -/
@[spec] theorem tls_vec.TlsVecU8.len_spec {T : Type} (self : tls_vec.TlsVecU8 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU8.len self ⦃ ⇓ r => ⌜ r.val = self.vec.val.length ⌝ ⦄ := by
  mvcgen [tls_vec.TlsVecU8.len]
  intro h; subst h; simp [Slice.len]

@[spec] theorem tls_vec.TlsByteVecU8.len_spec (self : tls_vec.TlsByteVecU8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU8.len self ⦃ ⇓ r => ⌜ r.val = self.vec.val.length ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU8.len]
  intro h; subst h; simp [Slice.len]

@[spec] theorem tls_vec.SecretTlsVecU8.len_spec {T : Type} (zeroizeZeroizeInst : zeroize.Zeroize T)
    (self : tls_vec.SecretTlsVecU8 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU8.len zeroizeZeroizeInst self ⦃ ⇓ r => ⌜ r.val = self.vec.val.length ⌝ ⦄ := by
  mvcgen [tls_vec.SecretTlsVecU8.len]
  intro h; subst h; simp [Slice.len]

/-- `TlsVecU16::len` is the length of the inner vector. -/
@[spec] theorem tls_vec.TlsVecU16.len_spec {T : Type} (self : tls_vec.TlsVecU16 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU16.len self ⦃ ⇓ r => ⌜ r.val = self.vec.val.length ⌝ ⦄ := by
  mvcgen [tls_vec.TlsVecU16.len]
  intro h; subst h; simp [Slice.len]

@[spec] theorem tls_vec.TlsByteVecU16.len_spec (self : tls_vec.TlsByteVecU16) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU16.len self ⦃ ⇓ r => ⌜ r.val = self.vec.val.length ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU16.len]
  intro h; subst h; simp [Slice.len]

@[spec] theorem tls_vec.SecretTlsVecU16.len_spec {T : Type} (zeroizeZeroizeInst : zeroize.Zeroize T)
    (self : tls_vec.SecretTlsVecU16 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU16.len zeroizeZeroizeInst self ⦃ ⇓ r => ⌜ r.val = self.vec.val.length ⌝ ⦄ := by
  mvcgen [tls_vec.SecretTlsVecU16.len]
  intro h; subst h; simp [Slice.len]

/-- `TlsVecU24::len` is the length of the inner vector. -/
@[spec] theorem tls_vec.TlsVecU24.len_spec {T : Type} (self : tls_vec.TlsVecU24 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU24.len self ⦃ ⇓ r => ⌜ r.val = self.vec.val.length ⌝ ⦄ := by
  mvcgen [tls_vec.TlsVecU24.len]
  intro h; subst h; simp [Slice.len]

@[spec] theorem tls_vec.TlsByteVecU24.len_spec (self : tls_vec.TlsByteVecU24) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU24.len self ⦃ ⇓ r => ⌜ r.val = self.vec.val.length ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU24.len]
  intro h; subst h; simp [Slice.len]

@[spec] theorem tls_vec.SecretTlsVecU24.len_spec {T : Type} (zeroizeZeroizeInst : zeroize.Zeroize T)
    (self : tls_vec.SecretTlsVecU24 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU24.len zeroizeZeroizeInst self ⦃ ⇓ r => ⌜ r.val = self.vec.val.length ⌝ ⦄ := by
  mvcgen [tls_vec.SecretTlsVecU24.len]
  intro h; subst h; simp [Slice.len]

/-- `TlsVecU32::len` is the length of the inner vector. -/
@[spec] theorem tls_vec.TlsVecU32.len_spec {T : Type} (self : tls_vec.TlsVecU32 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU32.len self ⦃ ⇓ r => ⌜ r.val = self.vec.val.length ⌝ ⦄ := by
  mvcgen [tls_vec.TlsVecU32.len]
  intro h; subst h; simp [Slice.len]

@[spec] theorem tls_vec.TlsByteVecU32.len_spec (self : tls_vec.TlsByteVecU32) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU32.len self ⦃ ⇓ r => ⌜ r.val = self.vec.val.length ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU32.len]
  intro h; subst h; simp [Slice.len]

@[spec] theorem tls_vec.SecretTlsVecU32.len_spec {T : Type} (zeroizeZeroizeInst : zeroize.Zeroize T)
    (self : tls_vec.SecretTlsVecU32 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU32.len zeroizeZeroizeInst self ⦃ ⇓ r => ⌜ r.val = self.vec.val.length ⌝ ⦄ := by
  mvcgen [tls_vec.SecretTlsVecU32.len]
  intro h; subst h; simp [Slice.len]

/-! ### `Vec::pop` length arithmetic -/

/-- Length arithmetic of the `pop` postconditions: `pop` removes the last element (if any), so the
new length is the old length minus `1` when an element was returned, and equal otherwise. -/
theorem pop_len_eq {α : Type} (l l' : List α) (o : Option α) (n m : Std.Usize)
    (r : UScalar UScalarTy.Usize)
    (ho : o = l.getLast?) (hl' : l' = l.dropLast) (hn : n.val = l.length) (hm : m.val = l'.length)
    (hr : r.val = n.val - (if o.isSome = true then 1#usize else 0#usize).val) : m = r := by
  subst ho hl'
  apply UScalar.eq_of_val_eq
  rcases l with _ | ⟨x, xs⟩
  · simp at hn hm hr ⊢
    omega
  · have hs : (List.getLast? (x :: xs)).isSome = true := by simp
    simp only [hs, if_true] at hr
    simp at hm hn hr
    omega

/-- `pop` returns an element iff the vector is non-empty. -/
theorem pop_isSome_eq {α : Type} (l : List α) (n : Std.Usize) (hn : n.val = l.length) :
    ((l.getLast?).isSome = true) = ¬ (decide (n = 0#usize) = true) := by
  rcases l with _ | ⟨x, xs⟩
  · have h0 : n = 0#usize := UScalar.eq_of_val_eq (by simpa using hn)
    simp [h0]
  · have h0 : n ≠ 0#usize := by
      intro h; subst h; simp at hn
    simp [h0]

/-- The amount `pop` subtracts from the length is at most the length. -/
theorem pop_sub_le {α : Type} (l : List α) (o : Option α) (n : Std.Usize)
    (ho : o = l.getLast?) (hn : n.val = l.length) :
    (if o.isSome = true then 1#usize else 0#usize).val ≤ n.val := by
  subst ho
  rcases l with _ | ⟨x, xs⟩
  · simp
  · have hs : (List.getLast? (x :: xs)).isSome = true := by simp
    simp only [hs, if_true]
    simp at hn ⊢
    omega

/-! ### FC closers -/

/-- Close the arithmetic VCs left by `mvcgen` on a post made of `len` calls: `decide`s become
props, `Slice.len` is unfolded, and `scalar_tac` finishes (also the `h_fail` panics, whose
hypotheses are contradictory). -/
syntax "fc_arith" : tactic
macro_rules
  | `(tactic| fc_arith) =>
    `(tactic| (all_goals (try simp only [decide_eq_true_eq, Slice.len] at *); all_goals scalar_tac))

/-! ### Partial triples with a trivial post -/

/-- A partial (`⇓?`) triple whose post is the constant `ok true` holds for any program: only
`ok` outcomes matter and the post cannot panic. -/
theorem partial_triple_ok_true {α : Type} (x : RustM α) (p : α → RustM Bool)
    (hp : ∀ a, p a = ok true) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓? a => ⌜ (p a).holds ⌝ ⦄ := by
  simp only [hp]
  cases x <;> simp [Std.Do.Triple, Std.Do.PostCond.mayThrow, RustM.holds]
    <;> simp [Std.Do.wp, Std.Do.PredTrans.apply]

/-- A partial (`⇓?`) triple from a statement about the `ok` outcomes only. -/
theorem partial_triple_of_ok {α : Type} {x : RustM α} {P : α → Prop}
    (h : ∀ r, x = ok r → P r) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓? r => ⌜ P r ⌝ ⦄ := by
  cases hx : x with
  | ok r =>
    have := h r hx
    simp [Std.Do.Triple, Std.Do.PostCond.mayThrow]
    simp [Std.Do.wp, Std.Do.PredTrans.apply, this]
  | fail e => simp [Std.Do.Triple, Std.Do.PostCond.mayThrow]; simp [Std.Do.wp, Std.Do.PredTrans.apply]
  | div => simp [Std.Do.Triple, Std.Do.PostCond.mayThrow]; simp [Std.Do.wp, Std.Do.PredTrans.apply]

/-- Converse: a partial (`⇓?`) triple gives its post on every `ok` outcome. -/
theorem ok_of_partial_triple {α : Type} {x : RustM α} {P : α → Prop} {r : α}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓? r => ⌜ P r ⌝ ⦄) (hr : x = ok r) : P r := by
  subst hr
  simpa [Std.Do.Triple, Std.Do.PostCond.mayThrow, Std.Do.wp, Std.Do.PredTrans.apply] using h

/-! ### Big-endian byte round trips -/

theorem fromBEBytes_toBEBytes_toNat {w : ℕ} (h : w % 8 = 0) (b : BitVec w) :
    (BitVec.fromBEBytes b.toBEBytes).toNat = b.toNat := by
  unfold BitVec.fromBEBytes BitVec.toBEBytes
  rw [BitVec.toNat_cast, List.reverse_reverse]
  have := congrArg BitVec.toNat (BitVec.fromLEBytes_toLEBytes h b)
  simpa using this

/-- Generic step: bytes made from a `BitVec` through `UScalar.mk` and read back through `U8.bv`. -/
theorem fromBEBytes_map_mk_toNat {w : ℕ} (h : w % 8 = 0) (b : BitVec w) :
    (BitVec.fromBEBytes (List.map U8.bv (List.map (@UScalar.mk UScalarTy.U8) b.toBEBytes))).toNat
      = b.toNat := by
  have key : List.map U8.bv (List.map (@UScalar.mk UScalarTy.U8) b.toBEBytes) = b.toBEBytes := by
    have hid : (U8.bv ∘ @UScalar.mk UScalarTy.U8) = id := rfl
    rw [List.map_map, hid, List.map_id]
  rw [key]
  exact fromBEBytes_toBEBytes_toNat h b

theorem U8_from_be_bytes_to_be_bytes (x : Std.U8) :
    Aeneas.Std.core.num.U8.from_be_bytes (Aeneas.Std.core.num.U8.to_be_bytes x) = x := by
  apply UScalar.eq_of_val_eq
  have h := fromBEBytes_map_mk_toNat (by decide : 8 % 8 = 0) x.bv
  unfold Aeneas.Std.core.num.U8.from_be_bytes Aeneas.Std.core.num.U8.to_be_bytes
  unfold UScalar.val
  rw [BitVec.toNat_cast]
  exact h

theorem U16_from_be_bytes_to_be_bytes (x : Std.U16) :
    Aeneas.Std.core.num.U16.from_be_bytes (Aeneas.Std.core.num.U16.to_be_bytes x) = x := by
  apply UScalar.eq_of_val_eq
  have h := fromBEBytes_map_mk_toNat (by decide : 16 % 8 = 0) x.bv
  unfold Aeneas.Std.core.num.U16.from_be_bytes Aeneas.Std.core.num.U16.to_be_bytes
  unfold UScalar.val
  rw [BitVec.toNat_cast]
  exact h

theorem U32_from_be_bytes_to_be_bytes (x : Std.U32) :
    Aeneas.Std.core.num.U32.from_be_bytes (Aeneas.Std.core.num.U32.to_be_bytes x) = x := by
  apply UScalar.eq_of_val_eq
  have h := fromBEBytes_map_mk_toNat (by decide : 32 % 8 = 0) x.bv
  unfold Aeneas.Std.core.num.U32.from_be_bytes Aeneas.Std.core.num.U32.to_be_bytes
  unfold UScalar.val
  rw [BitVec.toNat_cast]
  exact h

theorem U64_from_be_bytes_to_be_bytes (x : Std.U64) :
    Aeneas.Std.core.num.U64.from_be_bytes (Aeneas.Std.core.num.U64.to_be_bytes x) = x := by
  apply UScalar.eq_of_val_eq
  have h := fromBEBytes_map_mk_toNat (by decide : 64 % 8 = 0) x.bv
  unfold Aeneas.Std.core.num.U64.from_be_bytes Aeneas.Std.core.num.U64.to_be_bytes
  unfold UScalar.val
  rw [BitVec.toNat_cast]
  exact h

/-! The other direction: bytes → integer → bytes is the identity. -/

theorem toLEBytes_fromLEBytes (l : List Byte) : (BitVec.fromLEBytes l).toLEBytes = l := by
  apply List.ext_getElem
  · simp only [BitVec.toLEBytes_length]; omega
  · intro i h1 h2
    rw [Byte.eq_iff]
    intro j hj
    have := BitVec.toLEBytes_getElem!_testBit (BitVec.fromLEBytes l) i j hj
    have e1 := List.Inhabited_getElem_eq_getElem! (BitVec.fromLEBytes l).toLEBytes i h1
    have e2 := List.Inhabited_getElem_eq_getElem! l i h2
    rw [← e1] at this
    rw [this, BitVec.fromLEBytes_getElem!]
    have h3 : (8 * i + j) / 8 = i := by omega
    have h4 : (8 * i + j) % 8 = j := by omega
    rw [h3, h4, ← e2]

theorem toBEBytes_cast {n m : ℕ} (x : BitVec n) (h : n = m) :
    (x.cast h).toBEBytes = x.toBEBytes := by
  subst h; rfl

theorem toBEBytes_fromBEBytes (l : List Byte) : (BitVec.fromBEBytes l).toBEBytes = l := by
  unfold BitVec.fromBEBytes BitVec.toBEBytes
  have : ∀ {n m : ℕ} (x : BitVec n) (h : n = m), (x.cast h).toLEBytes = x.toLEBytes := by
    intro n m x h; subst h; rfl
  rw [this, toLEBytes_fromLEBytes, List.reverse_reverse]

theorem be_bytes_roundtrip (l : List Std.U8) {m : ℕ} (h : 8 * (List.map U8.bv l).length = m) :
    List.map (@UScalar.mk UScalarTy.U8)
      (BitVec.toBEBytes (BitVec.cast h (BitVec.fromBEBytes (List.map U8.bv l)))) = l := by
  rw [toBEBytes_cast, toBEBytes_fromBEBytes, List.map_map]
  have hid : ((@UScalar.mk UScalarTy.U8) ∘ U8.bv) = id := rfl
  rw [hid, List.map_id]

theorem U8_to_be_bytes_from_be_bytes (a : Aeneas.Std.Array Std.U8 1#usize) :
    Aeneas.Std.core.num.U8.to_be_bytes (Aeneas.Std.core.num.U8.from_be_bytes a) = a := by
  apply Subtype.ext
  have ha : a.val.length = 1 := by simpa using a.property
  unfold Aeneas.Std.core.num.U8.to_be_bytes Aeneas.Std.core.num.U8.from_be_bytes
  exact be_bytes_roundtrip a.val (by simp [ha])

theorem U16_to_be_bytes_from_be_bytes (a : Aeneas.Std.Array Std.U8 2#usize) :
    Aeneas.Std.core.num.U16.to_be_bytes (Aeneas.Std.core.num.U16.from_be_bytes a) = a := by
  apply Subtype.ext
  have ha : a.val.length = 2 := by simpa using a.property
  unfold Aeneas.Std.core.num.U16.to_be_bytes Aeneas.Std.core.num.U16.from_be_bytes
  exact be_bytes_roundtrip a.val (by simp [ha])

theorem U32_to_be_bytes_from_be_bytes (a : Aeneas.Std.Array Std.U8 4#usize) :
    Aeneas.Std.core.num.U32.to_be_bytes (Aeneas.Std.core.num.U32.from_be_bytes a) = a := by
  apply Subtype.ext
  have ha : a.val.length = 4 := by simpa using a.property
  unfold Aeneas.Std.core.num.U32.to_be_bytes Aeneas.Std.core.num.U32.from_be_bytes
  exact be_bytes_roundtrip a.val (by simp [ha])

theorem U64_to_be_bytes_from_be_bytes (a : Aeneas.Std.Array Std.U8 8#usize) :
    Aeneas.Std.core.num.U64.to_be_bytes (Aeneas.Std.core.num.U64.from_be_bytes a) = a := by
  apply Subtype.ext
  have ha : a.val.length = 8 := by simpa using a.property
  unfold Aeneas.Std.core.num.U64.to_be_bytes Aeneas.Std.core.num.U64.from_be_bytes
  exact be_bytes_roundtrip a.val (by simp [ha])

/-- `Option::ok_or` result is `Ok v`: the option was `some v`. -/
theorem ok_or_eq_ok {α E : Type} {o : core.option.Option α} {e : E}
    {r : core.result.Result α E} {v : α}
    (h : r = match o with | some x => .Ok x | none => .Err e) (hv : r = .Ok v) : o = some v := by
  subst h
  cases o with
  | none => cases hv
  | some x => simp only [core.result.Result.Ok.injEq] at hv; rw [hv]

/-- `Option::ok_or` result is an `Err`: the option was `none`. -/
theorem ok_or_eq_err {α E : Type} {o : core.option.Option α} {e e' : E}
    {r : core.result.Result α E}
    (h : r = match o with | some x => .Ok x | none => .Err e) (hv : r = .Err e') :
    o = none ∧ e' = e := by
  subst h
  cases o with
  | none => simp only [core.result.Result.Err.injEq] at hv; exact ⟨rfl, hv.symm⟩
  | some x => cases hv

/-- Exact behaviour of `u8::tls_deserialize_bytes`. -/
theorem U8_deserialize_char (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ U8.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes bytes
    ⦃ ⇓ r => ⌜ (1 ≤ bytes.val.length → ∃ (a : Aeneas.Std.Array Std.U8 1#usize) (t : Slice Std.U8),
          a.val = bytes.val.take 1 ∧ t.val = bytes.val.drop 1 ∧
          r = .Ok (Aeneas.Std.core.num.U8.from_be_bytes a, t)) ∧
        (bytes.val.length < 1 → r = .Err Error.EndOfStream) ⌝ ⦄ := by
  mvcgen [U8.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes,
    core.option.Option.ok_or_spec, core.result.Result.map_err_spec, core.mem.size_of_U8,
    primitives.DeserializeBytesU8.tls_deserialize_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorError.call_once]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  · rename_i o1 hs1 res1 hr1 cf1 v1 hcf1 tf hs3 t hteq cf2 v2 hcf2 b hb o2 hs2 res2 hr2 cf3 v3 hcf3 hv1 hv2 hv3
    have ho1 := ok_or_eq_ok hr1 hv1
    by_cases hl : 1 ≤ bytes.val.length
    · obtain ⟨t1, ho1', ht1⟩ := hs1.1 (by scalar_tac)
      rw [ho1] at ho1'
      have hv1t := Option.some.inj ho1'
      subst hv1t
      have hlen1 : v1.val.length = 1 := by rw [ht1]; simp [hl]
      obtain ⟨a0, hta0, ha0⟩ := hs3.1 (by scalar_tac)
      rw [hteq] at hta0
      have h1 := core.result.Result.Ok.inj hta0
      have h2 := core.result.Result.Ok.inj hv2
      obtain ⟨t2, ho2', ht2⟩ := hs2.1 (by scalar_tac)
      have ho2 := ok_or_eq_ok hr2 hv3
      rw [ho2] at ho2'
      have hv3t := Option.some.inj ho2'
      subst hv3t
      refine ⟨fun _ => ⟨v2, v3, ?_, ht2, ?_⟩, fun h => absurd h (by omega)⟩
      · rw [← h2, h1, ha0, ht1]; rfl
      · rw [hb]
    · exfalso
      have := hs1.2 (by scalar_tac)
      rw [ho1] at this
      cases this
  · rename_i o1 hs1 res1 hr1 cf1 v1 hcf1 tf hs3 t hteq cf2 v2 hcf2 b hb o2 hs2 res2 hr2 cf3 resid hcf3 e hres2 r hv1 hv2
    exfalso
    have ho1 := ok_or_eq_ok hr1 hv1
    have hl : 1 ≤ bytes.val.length := by
      by_contra hn
      have := hs1.2 (by scalar_tac)
      rw [ho1] at this
      cases this
    obtain ⟨t2, ho2', ht2⟩ := hs2.1 (by scalar_tac)
    obtain ⟨ho2, _⟩ := ok_or_eq_err hr2 hres2
    rw [ho2] at ho2'
    cases ho2'
  · rename_i o1 hs1 res1 hr1 cf1 v1 hcf1 tf hs3 e hte hv1
    exfalso
    have ho1 := ok_or_eq_ok hr1 hv1
    have hl : 1 ≤ bytes.val.length := by
      by_contra hn
      have := hs1.2 (by scalar_tac)
      rw [ho1] at this
      cases this
    obtain ⟨t1, ho1', ht1⟩ := hs1.1 (by scalar_tac)
    rw [ho1] at ho1'
    have hv1t := Option.some.inj ho1'
    subst hv1t
    have hlen1 : v1.val.length = 1 := by rw [ht1]; simp [hl]
    obtain ⟨a0, hta0, ha0⟩ := hs3.1 (by scalar_tac)
    rw [hte] at hta0
    cases hta0
  · rename_i o1 hs1 res1 hr1 cf1 resid hcf1 e hres1 r
    intro hre
    obtain ⟨ho1, he⟩ := ok_or_eq_err hr1 hres1
    have hl : bytes.val.length < 1 := by
      by_contra hn
      obtain ⟨t1, ho1', _⟩ := hs1.1 (by scalar_tac)
      rw [ho1] at ho1'
      cases ho1'
    subst hre
    subst he
    exact ⟨fun h => absurd h (by omega), fun _ => rfl⟩

/-- Exact behaviour of `u16::tls_deserialize_bytes`. -/
theorem U16_deserialize_char (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ U16.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes bytes
    ⦃ ⇓ r => ⌜ (2 ≤ bytes.val.length → ∃ (a : Aeneas.Std.Array Std.U8 2#usize) (t : Slice Std.U8),
          a.val = bytes.val.take 2 ∧ t.val = bytes.val.drop 2 ∧
          r = .Ok (Aeneas.Std.core.num.U16.from_be_bytes a, t)) ∧
        (bytes.val.length < 2 → r = .Err Error.EndOfStream) ⌝ ⦄ := by
  mvcgen [U16.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes,
    core.option.Option.ok_or_spec, core.result.Result.map_err_spec, core.mem.size_of_U16,
    primitives.DeserializeBytesU16.tls_deserialize_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorError.call_once]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  · rename_i o1 hs1 res1 hr1 cf1 v1 hcf1 tf hs3 t hteq cf2 v2 hcf2 b hb o2 hs2 res2 hr2 cf3 v3 hcf3 hv1 hv2 hv3
    have ho1 := ok_or_eq_ok hr1 hv1
    by_cases hl : 2 ≤ bytes.val.length
    · obtain ⟨t1, ho1', ht1⟩ := hs1.1 (by scalar_tac)
      rw [ho1] at ho1'
      have hv1t := Option.some.inj ho1'
      subst hv1t
      have hlen1 : v1.val.length = 2 := by rw [ht1]; simp [hl]
      obtain ⟨a0, hta0, ha0⟩ := hs3.1 (by scalar_tac)
      rw [hteq] at hta0
      have h1 := core.result.Result.Ok.inj hta0
      have h2 := core.result.Result.Ok.inj hv2
      obtain ⟨t2, ho2', ht2⟩ := hs2.1 (by scalar_tac)
      have ho2 := ok_or_eq_ok hr2 hv3
      rw [ho2] at ho2'
      have hv3t := Option.some.inj ho2'
      subst hv3t
      refine ⟨fun _ => ⟨v2, v3, ?_, ht2, ?_⟩, fun h => absurd h (by omega)⟩
      · rw [← h2, h1, ha0, ht1]; rfl
      · rw [hb]
    · exfalso
      have := hs1.2 (by scalar_tac)
      rw [ho1] at this
      cases this
  · rename_i o1 hs1 res1 hr1 cf1 v1 hcf1 tf hs3 t hteq cf2 v2 hcf2 b hb o2 hs2 res2 hr2 cf3 resid hcf3 e hres2 r hv1 hv2
    exfalso
    have ho1 := ok_or_eq_ok hr1 hv1
    have hl : 2 ≤ bytes.val.length := by
      by_contra hn
      have := hs1.2 (by scalar_tac)
      rw [ho1] at this
      cases this
    obtain ⟨t2, ho2', ht2⟩ := hs2.1 (by scalar_tac)
    obtain ⟨ho2, _⟩ := ok_or_eq_err hr2 hres2
    rw [ho2] at ho2'
    cases ho2'
  · rename_i o1 hs1 res1 hr1 cf1 v1 hcf1 tf hs3 e hte hv1
    exfalso
    have ho1 := ok_or_eq_ok hr1 hv1
    have hl : 2 ≤ bytes.val.length := by
      by_contra hn
      have := hs1.2 (by scalar_tac)
      rw [ho1] at this
      cases this
    obtain ⟨t1, ho1', ht1⟩ := hs1.1 (by scalar_tac)
    rw [ho1] at ho1'
    have hv1t := Option.some.inj ho1'
    subst hv1t
    have hlen1 : v1.val.length = 2 := by rw [ht1]; simp [hl]
    obtain ⟨a0, hta0, ha0⟩ := hs3.1 (by scalar_tac)
    rw [hte] at hta0
    cases hta0
  · rename_i o1 hs1 res1 hr1 cf1 resid hcf1 e hres1 r
    intro hre
    obtain ⟨ho1, he⟩ := ok_or_eq_err hr1 hres1
    have hl : bytes.val.length < 2 := by
      by_contra hn
      obtain ⟨t1, ho1', _⟩ := hs1.1 (by scalar_tac)
      rw [ho1] at ho1'
      cases ho1'
    subst hre
    subst he
    exact ⟨fun h => absurd h (by omega), fun _ => rfl⟩

/-- Exact behaviour of `u32::tls_deserialize_bytes`. -/
theorem U32_deserialize_char (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ U32.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes bytes
    ⦃ ⇓ r => ⌜ (4 ≤ bytes.val.length → ∃ (a : Aeneas.Std.Array Std.U8 4#usize) (t : Slice Std.U8),
          a.val = bytes.val.take 4 ∧ t.val = bytes.val.drop 4 ∧
          r = .Ok (Aeneas.Std.core.num.U32.from_be_bytes a, t)) ∧
        (bytes.val.length < 4 → r = .Err Error.EndOfStream) ⌝ ⦄ := by
  mvcgen [U32.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes,
    core.option.Option.ok_or_spec, core.result.Result.map_err_spec, core.mem.size_of_U32,
    primitives.DeserializeBytesU32.tls_deserialize_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorError.call_once]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  · rename_i o1 hs1 res1 hr1 cf1 v1 hcf1 tf hs3 t hteq cf2 v2 hcf2 b hb o2 hs2 res2 hr2 cf3 v3 hcf3 hv1 hv2 hv3
    have ho1 := ok_or_eq_ok hr1 hv1
    by_cases hl : 4 ≤ bytes.val.length
    · obtain ⟨t1, ho1', ht1⟩ := hs1.1 (by scalar_tac)
      rw [ho1] at ho1'
      have hv1t := Option.some.inj ho1'
      subst hv1t
      have hlen1 : v1.val.length = 4 := by rw [ht1]; simp [hl]
      obtain ⟨a0, hta0, ha0⟩ := hs3.1 (by scalar_tac)
      rw [hteq] at hta0
      have h1 := core.result.Result.Ok.inj hta0
      have h2 := core.result.Result.Ok.inj hv2
      obtain ⟨t2, ho2', ht2⟩ := hs2.1 (by scalar_tac)
      have ho2 := ok_or_eq_ok hr2 hv3
      rw [ho2] at ho2'
      have hv3t := Option.some.inj ho2'
      subst hv3t
      refine ⟨fun _ => ⟨v2, v3, ?_, ht2, ?_⟩, fun h => absurd h (by omega)⟩
      · rw [← h2, h1, ha0, ht1]; rfl
      · rw [hb]
    · exfalso
      have := hs1.2 (by scalar_tac)
      rw [ho1] at this
      cases this
  · rename_i o1 hs1 res1 hr1 cf1 v1 hcf1 tf hs3 t hteq cf2 v2 hcf2 b hb o2 hs2 res2 hr2 cf3 resid hcf3 e hres2 r hv1 hv2
    exfalso
    have ho1 := ok_or_eq_ok hr1 hv1
    have hl : 4 ≤ bytes.val.length := by
      by_contra hn
      have := hs1.2 (by scalar_tac)
      rw [ho1] at this
      cases this
    obtain ⟨t2, ho2', ht2⟩ := hs2.1 (by scalar_tac)
    obtain ⟨ho2, _⟩ := ok_or_eq_err hr2 hres2
    rw [ho2] at ho2'
    cases ho2'
  · rename_i o1 hs1 res1 hr1 cf1 v1 hcf1 tf hs3 e hte hv1
    exfalso
    have ho1 := ok_or_eq_ok hr1 hv1
    have hl : 4 ≤ bytes.val.length := by
      by_contra hn
      have := hs1.2 (by scalar_tac)
      rw [ho1] at this
      cases this
    obtain ⟨t1, ho1', ht1⟩ := hs1.1 (by scalar_tac)
    rw [ho1] at ho1'
    have hv1t := Option.some.inj ho1'
    subst hv1t
    have hlen1 : v1.val.length = 4 := by rw [ht1]; simp [hl]
    obtain ⟨a0, hta0, ha0⟩ := hs3.1 (by scalar_tac)
    rw [hte] at hta0
    cases hta0
  · rename_i o1 hs1 res1 hr1 cf1 resid hcf1 e hres1 r
    intro hre
    obtain ⟨ho1, he⟩ := ok_or_eq_err hr1 hres1
    have hl : bytes.val.length < 4 := by
      by_contra hn
      obtain ⟨t1, ho1', _⟩ := hs1.1 (by scalar_tac)
      rw [ho1] at ho1'
      cases ho1'
    subst hre
    subst he
    exact ⟨fun h => absurd h (by omega), fun _ => rfl⟩

/-- Exact behaviour of `u64::tls_deserialize_bytes`. -/
theorem U64_deserialize_char (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ U64.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes bytes
    ⦃ ⇓ r => ⌜ (8 ≤ bytes.val.length → ∃ (a : Aeneas.Std.Array Std.U8 8#usize) (t : Slice Std.U8),
          a.val = bytes.val.take 8 ∧ t.val = bytes.val.drop 8 ∧
          r = .Ok (Aeneas.Std.core.num.U64.from_be_bytes a, t)) ∧
        (bytes.val.length < 8 → r = .Err Error.EndOfStream) ⌝ ⦄ := by
  mvcgen [U64.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes,
    core.option.Option.ok_or_spec, core.result.Result.map_err_spec, core.mem.size_of_U64,
    primitives.DeserializeBytesU64.tls_deserialize_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorError.call_once]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  · rename_i o1 hs1 res1 hr1 cf1 v1 hcf1 tf hs3 t hteq cf2 v2 hcf2 b hb o2 hs2 res2 hr2 cf3 v3 hcf3 hv1 hv2 hv3
    have ho1 := ok_or_eq_ok hr1 hv1
    by_cases hl : 8 ≤ bytes.val.length
    · obtain ⟨t1, ho1', ht1⟩ := hs1.1 (by scalar_tac)
      rw [ho1] at ho1'
      have hv1t := Option.some.inj ho1'
      subst hv1t
      have hlen1 : v1.val.length = 8 := by rw [ht1]; simp [hl]
      obtain ⟨a0, hta0, ha0⟩ := hs3.1 (by scalar_tac)
      rw [hteq] at hta0
      have h1 := core.result.Result.Ok.inj hta0
      have h2 := core.result.Result.Ok.inj hv2
      obtain ⟨t2, ho2', ht2⟩ := hs2.1 (by scalar_tac)
      have ho2 := ok_or_eq_ok hr2 hv3
      rw [ho2] at ho2'
      have hv3t := Option.some.inj ho2'
      subst hv3t
      refine ⟨fun _ => ⟨v2, v3, ?_, ht2, ?_⟩, fun h => absurd h (by omega)⟩
      · rw [← h2, h1, ha0, ht1]; rfl
      · rw [hb]
    · exfalso
      have := hs1.2 (by scalar_tac)
      rw [ho1] at this
      cases this
  · rename_i o1 hs1 res1 hr1 cf1 v1 hcf1 tf hs3 t hteq cf2 v2 hcf2 b hb o2 hs2 res2 hr2 cf3 resid hcf3 e hres2 r hv1 hv2
    exfalso
    have ho1 := ok_or_eq_ok hr1 hv1
    have hl : 8 ≤ bytes.val.length := by
      by_contra hn
      have := hs1.2 (by scalar_tac)
      rw [ho1] at this
      cases this
    obtain ⟨t2, ho2', ht2⟩ := hs2.1 (by scalar_tac)
    obtain ⟨ho2, _⟩ := ok_or_eq_err hr2 hres2
    rw [ho2] at ho2'
    cases ho2'
  · rename_i o1 hs1 res1 hr1 cf1 v1 hcf1 tf hs3 e hte hv1
    exfalso
    have ho1 := ok_or_eq_ok hr1 hv1
    have hl : 8 ≤ bytes.val.length := by
      by_contra hn
      have := hs1.2 (by scalar_tac)
      rw [ho1] at this
      cases this
    obtain ⟨t1, ho1', ht1⟩ := hs1.1 (by scalar_tac)
    rw [ho1] at ho1'
    have hv1t := Option.some.inj ho1'
    subst hv1t
    have hlen1 : v1.val.length = 8 := by rw [ht1]; simp [hl]
    obtain ⟨a0, hta0, ha0⟩ := hs3.1 (by scalar_tac)
    rw [hte] at hta0
    cases hta0
  · rename_i o1 hs1 res1 hr1 cf1 resid hcf1 e hres1 r
    intro hre
    obtain ⟨ho1, he⟩ := ok_or_eq_err hr1 hres1
    have hl : bytes.val.length < 8 := by
      by_contra hn
      obtain ⟨t1, ho1', _⟩ := hs1.1 (by scalar_tac)
      rw [ho1] at ho1'
      cases ho1'
    subst hre
    subst he
    exact ⟨fun h => absurd h (by omega), fun _ => rfl⟩

/-- Exact behaviour of `u8::tls_serialize_bytes`: never fails, returns the big-endian bytes. -/
@[spec] theorem U8_serialize_char (x : Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ U8.Insts.Tls_codecSerializeBytes.tls_serialize_bytes x
    ⦃ ⇓ r => ⌜ ∃ v : alloc.vec.Vec Std.U8, r = .Ok v ∧
        (v : Slice Std.U8).val = (Aeneas.Std.core.num.U8.to_be_bytes x).val ⌝ ⦄ := by
  mvcgen [U8.Insts.Tls_codecSerializeBytes.tls_serialize_bytes,
    Shared0U8.Insts.Tls_codecSerializeBytes.tls_serialize_bytes]
  exact ⟨_, rfl, by simp [Aeneas.Std.Array.to_slice, *]⟩

/-- Exact behaviour of `u16::tls_serialize_bytes`: never fails, returns the big-endian bytes. -/
@[spec] theorem U16_serialize_char (x : Std.U16) :
    ⦃ ⌜ True ⌝ ⦄ U16.Insts.Tls_codecSerializeBytes.tls_serialize_bytes x
    ⦃ ⇓ r => ⌜ ∃ v : alloc.vec.Vec Std.U8, r = .Ok v ∧
        (v : Slice Std.U8).val = (Aeneas.Std.core.num.U16.to_be_bytes x).val ⌝ ⦄ := by
  mvcgen [U16.Insts.Tls_codecSerializeBytes.tls_serialize_bytes,
    Shared0U16.Insts.Tls_codecSerializeBytes.tls_serialize_bytes]
  exact ⟨_, rfl, by simp [Aeneas.Std.Array.to_slice, *]⟩

/-- Exact behaviour of `u32::tls_serialize_bytes`: never fails, returns the big-endian bytes. -/
@[spec] theorem U32_serialize_char (x : Std.U32) :
    ⦃ ⌜ True ⌝ ⦄ U32.Insts.Tls_codecSerializeBytes.tls_serialize_bytes x
    ⦃ ⇓ r => ⌜ ∃ v : alloc.vec.Vec Std.U8, r = .Ok v ∧
        (v : Slice Std.U8).val = (Aeneas.Std.core.num.U32.to_be_bytes x).val ⌝ ⦄ := by
  mvcgen [U32.Insts.Tls_codecSerializeBytes.tls_serialize_bytes,
    Shared0U32.Insts.Tls_codecSerializeBytes.tls_serialize_bytes]
  exact ⟨_, rfl, by simp [Aeneas.Std.Array.to_slice, *]⟩

/-- Exact behaviour of `u64::tls_serialize_bytes`: never fails, returns the big-endian bytes. -/
@[spec] theorem U64_serialize_char (x : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄ U64.Insts.Tls_codecSerializeBytes.tls_serialize_bytes x
    ⦃ ⇓ r => ⌜ ∃ v : alloc.vec.Vec Std.U8, r = .Ok v ∧
        (v : Slice Std.U8).val = (Aeneas.Std.core.num.U64.to_be_bytes x).val ⌝ ⦄ := by
  mvcgen [U64.Insts.Tls_codecSerializeBytes.tls_serialize_bytes,
    Shared0U64.Insts.Tls_codecSerializeBytes.tls_serialize_bytes]
  exact ⟨_, rfl, by simp [Aeneas.Std.Array.to_slice, *]⟩

/-- The body of the closures of the `*_decode_encode` posts:
`bytes.get(..consumed) == Some(out.as_slice())`. -/
def prefixCheck (c : Slice Std.U8) (tupled_args : (alloc.vec.Vec Std.U8) × Std.Usize) :
    RustM Bool := do
  let (out, consumed) := tupled_args
  let o ← core.slice.Slice.get
    (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8) c
    { «end» := consumed }
  let s ← alloc.vec.Vec.as_slice out
  core.option.Option.Insts.CoreCmpPartialEqOption.eq
    (core.Shared1A.Insts.CoreCmpPartialEqShared0B
    (core.Slice.Insts.CoreCmpPartialEqSlice core.U8.Insts.CoreCmpPartialEqU8))
    o (core.option.Option.Some s)

theorem prefixCheck_spec (c : Slice Std.U8) (out : alloc.vec.Vec Std.U8) (consumed : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ prefixCheck c (out, consumed)
    ⦃ ⇓ r => ⌜ r = true ↔ (consumed.val ≤ c.val.length ∧ c.val.take consumed.val = out.val) ⌝ ⦄ := by
  unfold prefixCheck
  have hs := core.Slice.Insts.CoreCmpPartialEqSlice.eq_spec core.U8.Insts.CoreCmpPartialEqU8
    (heq := core.U8.Insts.CoreCmpPartialEqU8.eq_decide_spec)
  have hdec : ∀ x y : Slice Std.U8, decide (x = y) = decide (x.val = y.val) := by
    intro x y
    have : x = y ↔ x.val = y.val := ⟨fun h => by rw [h], fun h => Subtype.ext h⟩
    simp only [this]
  have hs1 : ∀ x y : Slice Std.U8, ⦃ ⌜ True ⌝ ⦄
      (core.Shared1A.Insts.CoreCmpPartialEqShared0B
        (core.Slice.Insts.CoreCmpPartialEqSlice core.U8.Insts.CoreCmpPartialEqU8)).eq x y
      ⦃ ⇓ r => ⌜ r = decide (x = y) ⌝ ⦄ := by
    intro x y
    rw [hdec]
    exact hs x y
  mvcgen [core.option.Option.Insts.CoreCmpPartialEqOption.eq_spec, hs1]
  rename_i o ho s hs' r
  intro hr
  subst hr hs'
  rw [decide_eq_true_iff]
  constructor
  · intro h
    by_cases hle : consumed.val ≤ c.val.length
    · obtain ⟨t, rfl, ht⟩ := ho.1 hle
      have := Option.some.inj h
      subst this
      exact ⟨hle, ht.symm⟩
    · have := ho.2 (by omega)
      rw [this] at h
      cases h
  · rintro ⟨hle, htk⟩
    obtain ⟨t, rfl, ht⟩ := ho.1 hle
    congr 1
    exact Subtype.ext (ht.trans htk)

/-- Exact behaviour of `U24::tls_deserialize_bytes`. -/
theorem U24_deserialize_char (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ U24.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes bytes
    ⦃ ⇓ r => ⌜ (3 ≤ bytes.val.length → ∃ (a : Aeneas.Std.Array Std.U8 3#usize) (t : Slice Std.U8),
          a.val = bytes.val.take 3 ∧ t.val = bytes.val.drop 3 ∧
          r = .Ok (a, t)) ∧
        (bytes.val.length < 3 → r = .Err Error.EndOfStream) ⌝ ⦄ := by
  mvcgen [U24.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes,
    core.option.Option.ok_or_spec, core.result.Result.map_err_spec, core.mem.size_of_U24, U24.from_be_bytes,
    primitives.DeserializeBytesU24.tls_deserialize_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorError.call_once]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  · rename_i o1 hs1 res1 hr1 cf1 v1 hcf1 tf hs3 t hteq cf2 v2 hcf2 o2 hs2 res2 hr2 cf3 v3 hcf3 hv1 hv2 hv3
    have ho1 := ok_or_eq_ok hr1 hv1
    by_cases hl : 3 ≤ bytes.val.length
    · obtain ⟨t1, ho1', ht1⟩ := hs1.1 (by scalar_tac)
      rw [ho1] at ho1'
      have hv1t := Option.some.inj ho1'
      subst hv1t
      have hlen1 : v1.val.length = 3 := by rw [ht1]; simp [hl]
      obtain ⟨a0, hta0, ha0⟩ := hs3.1 (by scalar_tac)
      rw [hteq] at hta0
      have h1 := core.result.Result.Ok.inj hta0
      have h2 := core.result.Result.Ok.inj hv2
      obtain ⟨t2, ho2', ht2⟩ := hs2.1 (by scalar_tac)
      have ho2 := ok_or_eq_ok hr2 hv3
      rw [ho2] at ho2'
      have hv3t := Option.some.inj ho2'
      subst hv3t
      refine ⟨fun _ => ⟨v2, v3, ?_, ht2, ?_⟩, fun h => absurd h (by omega)⟩
      · rw [← h2, h1, ha0, ht1]; rfl
      · rfl
    · exfalso
      have := hs1.2 (by scalar_tac)
      rw [ho1] at this
      cases this
  · rename_i o1 hs1 res1 hr1 cf1 v1 hcf1 tf hs3 t hteq cf2 v2 hcf2 o2 hs2 res2 hr2 cf3 resid hcf3 e hres2 r hv1 hv2
    exfalso
    have ho1 := ok_or_eq_ok hr1 hv1
    have hl : 3 ≤ bytes.val.length := by
      by_contra hn
      have := hs1.2 (by scalar_tac)
      rw [ho1] at this
      cases this
    obtain ⟨t2, ho2', ht2⟩ := hs2.1 (by scalar_tac)
    obtain ⟨ho2, _⟩ := ok_or_eq_err hr2 hres2
    rw [ho2] at ho2'
    cases ho2'
  · rename_i o1 hs1 res1 hr1 cf1 v1 hcf1 tf hs3 e hte hv1
    exfalso
    have ho1 := ok_or_eq_ok hr1 hv1
    have hl : 3 ≤ bytes.val.length := by
      by_contra hn
      have := hs1.2 (by scalar_tac)
      rw [ho1] at this
      cases this
    obtain ⟨t1, ho1', ht1⟩ := hs1.1 (by scalar_tac)
    rw [ho1] at ho1'
    have hv1t := Option.some.inj ho1'
    subst hv1t
    have hlen1 : v1.val.length = 3 := by rw [ht1]; simp [hl]
    obtain ⟨a0, hta0, ha0⟩ := hs3.1 (by scalar_tac)
    rw [hte] at hta0
    cases hta0
  · rename_i o1 hs1 res1 hr1 cf1 resid hcf1 e hres1 r
    intro hre
    obtain ⟨ho1, he⟩ := ok_or_eq_err hr1 hres1
    have hl : bytes.val.length < 3 := by
      by_contra hn
      obtain ⟨t1, ho1', _⟩ := hs1.1 (by scalar_tac)
      rw [ho1] at ho1'
      cases ho1'
    subst hre
    subst he
    exact ⟨fun h => absurd h (by omega), fun _ => rfl⟩


/-- Exact behaviour of `[u8; LEN]::tls_deserialize_bytes`. -/
theorem ArrayU8LEN_deserialize_char (LEN : Std.Usize) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ ArrayU8LEN.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes LEN bytes
    ⦃ ⇓ r => ⌜ (LEN.val ≤ bytes.val.length → ∃ (a : Aeneas.Std.Array Std.U8 LEN) (t : Slice Std.U8),
          a.val = bytes.val.take LEN.val ∧ t.val = bytes.val.drop LEN.val ∧
          r = .Ok (a, t)) ∧
        (bytes.val.length < LEN.val → r = .Err Error.EndOfStream) ⌝ ⦄ := by
  unfold ArrayU8LEN.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes
  mvcgen [
    arrays.DeserializeBytesArrayU8LEN.tls_deserialize_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorError.call_once,
    core.option.Option.ok_or_spec, core.result.Result.map_err_spec, core.Slice.Insts.CoreOpsIndexIndex.index_spec,
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_spec]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  · rename_i o1 hs1 res1 hr1 cf1 v1 hcf1 tf hs3 t hteq cf2 v2 hcf2 o2 hv1 hv2
    intro hs2a hs2b
    have ho1 := ok_or_eq_ok hr1 hv1
    by_cases hl : LEN.val ≤ bytes.val.length
    · obtain ⟨t1, ho1', ht1⟩ := hs1.1 hl
      rw [ho1] at ho1'
      have hv1t := Option.some.inj ho1'
      subst hv1t
      have hlen1 : v1.val.length = LEN.val := by rw [ht1]; simp [hl]
      obtain ⟨a0, hta0, ha0⟩ := hs3.1 hlen1
      rw [hteq] at hta0
      have h1 := core.result.Result.Ok.inj hta0
      have h2 := core.result.Result.Ok.inj hv2
      obtain ⟨t2, ho2, ht2⟩ := hs2a hl
      refine ⟨t2, ho2, ?_⟩
      simp only [PostCond.ok]
      mvcgen
      refine ⟨fun _ => ⟨v2, t2, ?_, ht2, rfl⟩, fun h => absurd h (by omega)⟩
      rw [← h2, h1, ha0, ht1]
    · exfalso
      have := hs1.2 (by omega)
      rw [ho1] at this
      cases this
  · rename_i o1 hs1 res1 hr1 cf1 v1 hcf1 tf hs3 e hte r hv1
    exfalso
    have ho1 := ok_or_eq_ok hr1 hv1
    have hl : LEN.val ≤ bytes.val.length := by
      by_contra hn
      have := hs1.2 (by omega)
      rw [ho1] at this
      cases this
    obtain ⟨t1, ho1', ht1⟩ := hs1.1 hl
    rw [ho1] at ho1'
    have hv1t := Option.some.inj ho1'
    subst hv1t
    have hlen1 : v1.val.length = LEN.val := by rw [ht1]; simp [hl]
    obtain ⟨a0, hta0, ha0⟩ := hs3.1 hlen1
    rw [hte] at hta0
    cases hta0
  · rename_i o1 hs1 res1 hr1 cf1 resid hcf1 e hres1 r
    intro hre
    obtain ⟨ho1, he⟩ := ok_or_eq_err hr1 hres1
    have hl : bytes.val.length < LEN.val := by
      by_contra hn
      obtain ⟨t1, ho1', _⟩ := hs1.1 (by omega)
      rw [ho1] at ho1'
      cases ho1'
    subst hre
    subst he
    exact ⟨fun h => absurd h (by omega), fun _ => rfl⟩

/-- Exact behaviour of `U24::tls_serialize_bytes`: never fails, returns the three bytes. -/
@[spec] theorem U24_serialize_char (x : U24) :
    ⦃ ⌜ True ⌝ ⦄ U24.Insts.Tls_codecSerializeBytes.tls_serialize_bytes x
    ⦃ ⇓ r => ⌜ ∃ v : alloc.vec.Vec Std.U8, r = .Ok v ∧ (v : Slice Std.U8).val = x.val ⌝ ⦄ := by
  mvcgen [U24.Insts.Tls_codecSerializeBytes.tls_serialize_bytes,
    Shared0U24.Insts.Tls_codecSerializeBytes.tls_serialize_bytes, U24.to_be_bytes]
  exact ⟨_, rfl, by simp [Aeneas.Std.Array.to_slice, *]⟩

theorem U24_eq_spec (x y : U24) :
    ⦃ ⌜ True ⌝ ⦄ U24.Insts.CoreCmpPartialEqU24.eq x y
    ⦃ ⇓ r => ⌜ r = decide (x.val = y.val) ⌝ ⦄ := by
  unfold U24.Insts.CoreCmpPartialEqU24.eq
  exact core.Array.Insts.CoreCmpPartialEqArray.eq_spec _ x y
    core.U8.Insts.CoreCmpPartialEqU8.eq_decide_spec

/-- Exact behaviour of `[u8; LEN]::tls_serialize_bytes`: never fails, returns the bytes. -/
@[spec] theorem ArrayU8LEN_serialize_char {LEN : Std.Usize} (x : Aeneas.Std.Array Std.U8 LEN) :
    ⦃ ⌜ True ⌝ ⦄ ArrayU8LEN.Insts.Tls_codecSerializeBytes.tls_serialize_bytes x
    ⦃ ⇓ r => ⌜ ∃ v : alloc.vec.Vec Std.U8, r = .Ok v ∧ (v : Slice Std.U8).val = x.val ⌝ ⦄ := by
  mvcgen [ArrayU8LEN.Insts.Tls_codecSerializeBytes.tls_serialize_bytes]
  exact ⟨_, rfl, by simp [Aeneas.Std.Array.to_slice, *]⟩

/-- `==` on `[u8; N]`. -/
@[spec high] theorem Array_U8_eq_spec {N : Std.Usize} (a b : Aeneas.Std.Array Std.U8 N) :
    ⦃ ⌜ True ⌝ ⦄ core.Array.Insts.CoreCmpPartialEqArray.eq core.U8.Insts.CoreCmpPartialEqU8 a b
    ⦃ ⇓ r => ⌜ r = decide (a.val = b.val) ⌝ ⦄ :=
  core.Array.Insts.CoreCmpPartialEqArray.eq_spec _ a b core.U8.Insts.CoreCmpPartialEqU8.eq_decide_spec


/-! ### `TlsVarInt::write_bytes` -/

/-- One iteration of the `write_bytes` loops: needs `i ≤ len`, keeps the slice length. -/
theorem varint.TlsVarInt.write_bytes_loop0.body_spec (bytes : Slice Std.U8) (value : Std.U64)
    (i : Std.Usize) (h : i.val ≤ bytes.val.length) :
    ⦃ ⌜ True ⌝ ⦄ varint.TlsVarInt.write_bytes_loop0.body bytes value i
    ⦃ ⇓ r => ⌜ match r with
      | .done y => y.val.length = bytes.val.length
      | .cont (b', _, i') => b'.val.length = bytes.val.length ∧ i'.val ≤ b'.val.length ∧ i'.val < i.val ⌝ ⦄ := by
  unfold varint.TlsVarInt.write_bytes_loop0.body
  mvcgen
  · rename_i i1 hi1 hge i2 hi2 i3 hi3 i4 hi4 i5 hi5 s hlt hs v hv1 hv2 hlt8
    subst hs
    have hl : (bytes.set i1 i5).length = bytes.length := by simp [Slice.set, Slice.length]
    refine ⟨?_, ?_, ?_⟩ <;> scalar_tac
  · rename_i i1 hi1 hge i2 hi2 i3 hi3 i4 hi4 i5 hi5 hlt
    obtain ⟨hx, _⟩ := hi4
    exfalso; scalar_tac
  · exfalso; scalar_tac
  · exfalso; scalar_tac


/-- The `write_bytes` loops preserve the slice length (given `i ≤ len`). -/
theorem varint.TlsVarInt.write_bytes_loop0_spec (bytes : Slice Std.U8) (value : Std.U64)
    (i : Std.Usize) (h : i.val ≤ bytes.val.length) :
    ⦃ ⌜ True ⌝ ⦄ varint.TlsVarInt.write_bytes_loop0 bytes value i
    ⦃ ⇓ r => ⌜ r.val.length = bytes.val.length ⌝ ⦄ := by
  unfold varint.TlsVarInt.write_bytes_loop0
  apply Aeneas.Std.WP.spec_to_mvcgen
  apply Aeneas.Std.loop.spec_decr_nat
    (fun x : Slice Std.U8 × Std.U64 × Std.Usize => x.2.2.val)
    (fun x : Slice Std.U8 × Std.U64 × Std.Usize =>
      x.1.val.length = bytes.val.length ∧ x.2.2.val ≤ x.1.val.length)
    (fun y : Slice Std.U8 => y.val.length = bytes.val.length)
  · rintro ⟨b, v, j⟩ ⟨hb, hj⟩
    obtain ⟨r, hr, hP⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp
      (varint.TlsVarInt.write_bytes_loop0.body_spec b v j hj)
    dsimp only
    rw [hr, Aeneas.Std.WP.spec_ok]
    cases r with
    | done y => exact hP.trans hb
    | cont x =>
      obtain ⟨b', v', j'⟩ := x
      exact ⟨⟨hP.1.trans hb, hP.2.1⟩, hP.2.2⟩
  · exact ⟨rfl, h⟩


theorem varint.TlsVarInt.write_bytes_loop1_spec (bytes : Slice Std.U8) (value : Std.U64)
    (i : Std.Usize) (h : i.val ≤ bytes.val.length) :
    ⦃ ⌜ True ⌝ ⦄ varint.TlsVarInt.write_bytes_loop1 bytes value i
    ⦃ ⇓ r => ⌜ r.val.length = bytes.val.length ⌝ ⦄ := by
  have := varint.TlsVarInt.write_bytes_loop0_spec bytes value i h
  unfold varint.TlsVarInt.write_bytes_loop1 varint.TlsVarInt.write_bytes_loop1.body
  unfold varint.TlsVarInt.write_bytes_loop0 varint.TlsVarInt.write_bytes_loop0.body at this
  exact this

theorem varint.TlsVarInt.write_bytes_loop2_spec (bytes : Slice Std.U8) (value : Std.U64)
    (i : Std.Usize) (h : i.val ≤ bytes.val.length) :
    ⦃ ⌜ True ⌝ ⦄ varint.TlsVarInt.write_bytes_loop2 bytes value i
    ⦃ ⇓ r => ⌜ r.val.length = bytes.val.length ⌝ ⦄ := by
  have := varint.TlsVarInt.write_bytes_loop0_spec bytes value i h
  unfold varint.TlsVarInt.write_bytes_loop2 varint.TlsVarInt.write_bytes_loop2.body
  unfold varint.TlsVarInt.write_bytes_loop0 varint.TlsVarInt.write_bytes_loop0.body at this
  exact this

theorem varint.TlsVarInt.write_bytes_loop3_spec (bytes : Slice Std.U8) (value : Std.U64)
    (i : Std.Usize) (h : i.val ≤ bytes.val.length) :
    ⦃ ⌜ True ⌝ ⦄ varint.TlsVarInt.write_bytes_loop3 bytes value i
    ⦃ ⇓ r => ⌜ r.val.length = bytes.val.length ⌝ ⦄ := by
  have := varint.TlsVarInt.write_bytes_loop0_spec bytes value i h
  unfold varint.TlsVarInt.write_bytes_loop3 varint.TlsVarInt.write_bytes_loop3.body
  unfold varint.TlsVarInt.write_bytes_loop0 varint.TlsVarInt.write_bytes_loop0.body at this
  exact this


/-- Cloning a replicated `u8` list is the identity. -/
theorem mapM_clone_replicate_U8 (n : Nat) (x : Std.U8) :
    (List.replicate n x).mapM core.U8.Insts.CoreCloneClone.clone = ok (List.replicate n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.mapM_cons, ih]
    rfl

/-- `vec![x; len]` for `u8`: a vector of length `len`. -/
theorem alloc.vec.from_elem_U8_len_spec (item : Std.U8) (len : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ alloc.vec.from_elem core.U8.Insts.CoreCloneClone item len
    ⦃ ⇓ r => ⌜ (r : Slice Std.U8).val.length = len.val ⌝ ⦄ := by
  unfold alloc.vec.from_elem rust_primitives.sequence.seq_create
  mvcgen
  · rename_i h
    simp [Slice.new, h]
  · rename_i hne cl hcl comb hle
    have hl := List.mapM_RustM_length hcl
    simp only [List.length_replicate] at hl
    simp only [comb, List.length_append, List.length_singleton, hl]
    scalar_tac
  · rename_i hne cl hcl comb hle
    have hl := List.mapM_RustM_length hcl
    simp only [List.length_replicate] at hl
    exfalso; apply hle
    simp only [comb, List.length_append, List.length_singleton, hl]
    scalar_tac
  · rename_i hne e hcl
    rw [mapM_clone_replicate_U8] at hcl
    cases hcl
  · rename_i hne hcl
    rw [mapM_clone_replicate_U8] at hcl
    cases hcl

/-- Length of `take`, in the `Slice` form used by the write-back lemmas. -/
theorem slice_take_length (l : List Std.U8) (n : Nat) (h : n ≤ l.length) :
    (l.take n).length = n := by simp [h]

/-- Exact result of `TlsVarInt::write_bytes` (contents of the written bytes are not tracked):
too short a buffer is returned unchanged with `InvalidVectorLength`; otherwise it returns the
encoded length and a buffer of the same length. -/
theorem varint.TlsVarInt.write_bytes_spec (self : varint.TlsVarInt) (buf : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ varint.TlsVarInt.write_bytes self buf
    ⦃ ⇓ r => ⌜ (buf.val.length < varint.lenOf self.val →
                  r = (.Err Error.InvalidVectorLength, buf)) ∧
               (varint.lenOf self.val ≤ buf.val.length →
                  (∃ l : Std.Usize, r.1 = .Ok l ∧ l.val = varint.lenOf self.val) ∧
                  r.2.val.length = buf.val.length) ⌝ ⦄ := by
  mvcgen [varint.TlsVarInt.write_bytes, varint.TlsVarInt.write_bytes_loop0_spec,
    varint.TlsVarInt.write_bytes_loop1_spec, varint.TlsVarInt.write_bytes_loop2_spec,
    varint.TlsVarInt.write_bytes_loop3_spec]
  · rename_i len hlc blen hlt hbl
    have hc := varint.lenOf_char _ _ hlc
    refine ⟨fun _ => trivial, fun hle => ?_⟩
    exfalso; scalar_tac
  · rename_i len hlc blen hnlt hbl
    scalar_tac
  -- len = 1
  · rename_i len hlc blen hnlt hbl p hx hp s hlt hs
    have hc := varint.lenOf_char _ _ hlc
    have h2 : p.1.val.length = len.val := by rw [hp.1]; apply slice_take_length; scalar_tac
    have h3 : s.length = p.1.length := by rw [hs]; simp [Slice.set, Slice.length]
    scalar_tac
  · rename_i len hlc blen hnlt hbl p hx hp s hlt hs s2 buf1 hl2
    have hc := varint.lenOf_char _ _ hlc
    refine ⟨fun hlt' => ?_, fun hle => ⟨⟨_, rfl, ?_⟩, ?_⟩⟩
    · exfalso; scalar_tac
    · scalar_tac
    · change (p.2 s2).val.length = buf.val.length
      rw [hp.2 s2, List.length_setSlice!]
  · rename_i len hlc blen hnlt hbl p hx hp ha
    have hc := varint.lenOf_char _ _ hlc
    have h2 : p.1.val.length = len.val := by rw [hp.1]; apply slice_take_length; scalar_tac
    exfalso; scalar_tac
  -- len = 2
  · rename_i len hlc blen hnlt hbl p hx hp s hlt hs
    have hc := varint.lenOf_char _ _ hlc
    have h2 : p.1.val.length = len.val := by rw [hp.1]; apply slice_take_length; scalar_tac
    have h3 : s.length = p.1.length := by rw [hs]; simp [Slice.set, Slice.length]
    scalar_tac
  · rename_i len hlc blen hnlt hbl p hx hp s hlt hs s2 buf1 hl2
    have hc := varint.lenOf_char _ _ hlc
    refine ⟨fun hlt' => ?_, fun hle => ⟨⟨_, rfl, ?_⟩, ?_⟩⟩
    · exfalso; scalar_tac
    · scalar_tac
    · change (p.2 s2).val.length = buf.val.length
      rw [hp.2 s2, List.length_setSlice!]
  · rename_i len hlc blen hnlt hbl p hx hp ha
    have hc := varint.lenOf_char _ _ hlc
    have h2 : p.1.val.length = len.val := by rw [hp.1]; apply slice_take_length; scalar_tac
    exfalso; scalar_tac
  -- len = 4
  · rename_i len hlc blen hnlt hbl p hx hp s hlt hs
    have hc := varint.lenOf_char _ _ hlc
    have h2 : p.1.val.length = len.val := by rw [hp.1]; apply slice_take_length; scalar_tac
    have h3 : s.length = p.1.length := by rw [hs]; simp [Slice.set, Slice.length]
    scalar_tac
  · rename_i len hlc blen hnlt hbl p hx hp s hlt hs s2 buf1 hl2
    have hc := varint.lenOf_char _ _ hlc
    refine ⟨fun hlt' => ?_, fun hle => ⟨⟨_, rfl, ?_⟩, ?_⟩⟩
    · exfalso; scalar_tac
    · scalar_tac
    · change (p.2 s2).val.length = buf.val.length
      rw [hp.2 s2, List.length_setSlice!]
  · rename_i len hlc blen hnlt hbl p hx hp ha
    have hc := varint.lenOf_char _ _ hlc
    have h2 : p.1.val.length = len.val := by rw [hp.1]; apply slice_take_length; scalar_tac
    exfalso; scalar_tac
  -- len = 8
  · rename_i len hlc blen hnlt hbl p hx hp s hlt hs
    have hc := varint.lenOf_char _ _ hlc
    have h2 : p.1.val.length = len.val := by rw [hp.1]; apply slice_take_length; scalar_tac
    have h3 : s.length = p.1.length := by rw [hs]; simp [Slice.set, Slice.length]
    scalar_tac
  · rename_i len hlc blen hnlt hbl p hx hp s hlt hs s2 buf1 hl2
    have hc := varint.lenOf_char _ _ hlc
    refine ⟨fun hlt' => ?_, fun hle => ⟨⟨_, rfl, ?_⟩, ?_⟩⟩
    · exfalso; scalar_tac
    · scalar_tac
    · change (p.2 s2).val.length = buf.val.length
      rw [hp.2 s2, List.length_setSlice!]
  · rename_i len hlc blen hnlt hbl p hx hp ha
    have hc := varint.lenOf_char _ _ hlc
    have h2 : p.1.val.length = len.val := by rw [hp.1]; apply slice_take_length; scalar_tac
    exfalso; scalar_tac
  · rename_i len hlc blen hnlt hbl p n h1 h2 h4 h8 hx hp a1 a2
    have hc := varint.lenOf_char _ _ hlc
    have e1 : n ≠ 1 := h1
    have e2 : n ≠ 2 := h2
    have e4 : n ≠ 4 := h4
    have e8 : n ≠ 8 := h8
    exfalso; omega

/-- Exact behaviour of `TlsVarInt::tls_serialize_bytes`, on the length: never fails and returns
`lenOf` bytes. -/
theorem varint.TlsVarInt.serialize_len_char (self : varint.TlsVarInt) :
    ⦃ ⌜ True ⌝ ⦄ varint.TlsVarInt.Insts.Tls_codecSerializeBytes.tls_serialize_bytes self
    ⦃ ⇓ r => ⌜ ∃ v : alloc.vec.Vec Std.U8, r = .Ok v ∧
        (v : Slice Std.U8).val.length = varint.lenOf self.val ⌝ ⦄ := by
  mvcgen [varint.TlsVarInt.Insts.Tls_codecSerializeBytes.tls_serialize_bytes,
    varint.TlsVarInt.bytes_len_spec, alloc.vec.from_elem_U8_len_spec,
    varint.TlsVarInt.write_bytes_spec, alloc.vec.Vec.Insts.CoreOpsDerefDerefMutSlice.deref_mut,
    alloc.vec.Vec.as_mut_slice, rust_primitives.sequence.seq_to_slice_mut]
  · rename_i len hlc vec hvl back wr hwr cf val hx byt hcf
    have hc := varint.lenOf_char _ _ hlc
    have hle : varint.lenOf self.val ≤ vec.val.length := by scalar_tac
    obtain ⟨_, hlen⟩ := hwr.2 hle
    refine ⟨_, rfl, ?_⟩
    show wr.2.val.length = _
    omega
  · rename_i len hlc vec hvl back wr hwr cf resid hx
    have hc := varint.lenOf_char _ _ hlc
    have hle : varint.lenOf self.val ≤ vec.val.length := by scalar_tac
    obtain ⟨⟨l, hl, _⟩, _⟩ := hwr.2 hle
    intro hb
    rw [hl] at hb
    simp only [tryCF, reduceCtorEq] at hb

/-- `saturating_add` does not saturate for small operands. -/
theorem Usize_saturating_add_val (x y : Std.Usize) (h : x.val + y.val < 2 ^ 32) :
    (UScalar.saturating_add x y).val = x.val + y.val := by
  have hm : x.val + y.val ≤ UScalar.max UScalarTy.Usize := by
    rcases System.Platform.numBits_eq with h' | h' <;>
      simp [UScalar.max, UScalarTy.numBits, h'] <;> omega
  have hlt : x.val + y.val < 2 ^ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h' | h' <;> rw [h'] <;> omega
  unfold UScalar.saturating_add
  rw [min_eq_right hm]
  unfold UScalar.val
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hlt

/-! ### `Option<u16>` -/

/-- `Box<[T]>::into_vec`: the identity on the contents. -/
theorem alloc.slice.Slice.into_vec_spec {T : Type} (s : Slice T) :
    ⦃ ⌜ True ⌝ ⦄ alloc.slice.Slice.into_vec s ⦃ ⇓ r => ⌜ (r : Slice T) = s ⌝ ⦄ := by
  unfold alloc.slice.Slice.into_vec alloc.slice.Dummy.into_vec
    rust_primitives.sequence.seq_from_boxed_slice alloc.vec.from_seq
  mvcgen

/-- Exact behaviour of `Option<u16>::tls_serialize_bytes`: never fails, `0` or `1` followed by the
big-endian bytes. -/
theorem Option_U16_serialize_char (o : core.option.Option Std.U16) :
    ⦃ ⌜ True ⌝ ⦄ core.option.Option.Insts.Tls_codecSerializeBytes.tls_serialize_bytes
      U16.Insts.Tls_codecSerializeBytes o
    ⦃ ⇓ r => ⌜ ∃ v : alloc.vec.Vec Std.U8, r = .Ok v ∧
        (v : Slice Std.U8).val = (match o with
          | .none => [0#u8]
          | .some x => 1#u8 :: (Aeneas.Std.core.num.U16.to_be_bytes x).val) ⌝ ⦄ := by
  cases o with
  | none =>
    mvcgen [core.option.Option.Insts.Tls_codecSerializeBytes.tls_serialize_bytes,
      alloc.slice.Slice.into_vec_spec]
    refine ⟨_, rfl, ?_⟩
    simp_all [Std.Array.to_slice]
    rfl
  | some x =>
    mvcgen [core.option.Option.Insts.Tls_codecSerializeBytes.tls_serialize_bytes,
      U16.Insts.Tls_codecSize.tls_serialized_len, core.mem.size_of_U16, checked_alloc_len,
      checked_capacity, alloc.vec.Vec.with_capacity, alloc.vec.Vec.append,
      rust_primitives.sequence.seq_concat]
    · rename_i sat hsat hgt cf resid hx
      intro _
      exfalso
      have := Usize.hcast_Isize_MAX_val
      have h3 := Usize_saturating_add_val 2#usize 1#usize (by scalar_tac)
      rw [← hsat] at h3
      scalar_tac
    · rename_i sat hsat hle cf val hx hcf v hv
      subst hv
      have h0 : (Slice.new U8).val.length = 0 := rfl
      rw [h0]
      scalar_tac
    · rename_i sat hsat hle cf val hx hcf v0 hv0 v1 hv1 res hres cf1 val1 hx1 hcf1 comb hlen
      obtain ⟨v, rfl, hv⟩ := hres
      rw [continue_eq_tryCF, core.result.Result.Ok.injEq] at hcf1
      subst hcf1
      subst hv0
      refine ⟨⟨comb, hlen⟩, rfl, ?_⟩
      show comb = _
      simp only [comb, hv1, hv]
      rfl
    · rename_i sat hsat hle cf val hx hcf v0 hv0 v1 hv1 res hres cf1 val1 hx1 hcf1 comb hlen
      obtain ⟨v, rfl, hv⟩ := hres
      rw [continue_eq_tryCF, core.result.Result.Ok.injEq] at hcf1
      subst hcf1
      subst hv0
      have h2 : v.val.length = 2 := by
        rw [hv]; simpa using (Aeneas.Std.core.num.U16.to_be_bytes x).property
      exfalso; apply hlen
      simp only [comb, hv1, List.length_append, h2]
      simp [Slice.new]
      scalar_tac
    · rename_i sat hsat hle cf val hx hcf v0 hv0 v1 hv1 res hres cf1 resid hx1
      obtain ⟨v, rfl, hv⟩ := hres
      intro hb
      simp only [tryCF, reduceCtorEq] at hb
    · rename_i sat hsat hle cf resid hx
      intro hb
      simp only [tryCF, reduceCtorEq] at hb

theorem U8_to_be_bytes_val (x : Std.U8) : (Aeneas.Std.core.num.U8.to_be_bytes x).val = [x] := by
  unfold Aeneas.Std.core.num.U8.to_be_bytes
  simp [BitVec.toBEBytes]
  rw [BitVec.toLEBytes.eq_def]
  simp
  rw [BitVec.toLEBytes.eq_def]
  simp

theorem U8_from_be_bytes_of_val (a : Aeneas.Std.Array Std.U8 1#usize) (b : Std.U8)
    (h : a.val = [b]) : Aeneas.Std.core.num.U8.from_be_bytes a = b := by
  have h1 := U8_to_be_bytes_from_be_bytes a
  have h2 := congrArg Subtype.val h1
  rw [U8_to_be_bytes_val, h] at h2
  exact List.singleton_inj.mp h2

/-- Consequences of a successful `?` on the result of `u8::tls_deserialize_bytes`. -/
theorem U8_deserialize_ok {bytes : Slice Std.U8} {r : core.result.Result (Std.U8 × Slice Std.U8) Error}
    {p : Std.U8 × Slice Std.U8}
    (hP : (1 ≤ bytes.val.length → ∃ (a : Aeneas.Std.Array Std.U8 1#usize) (t : Slice Std.U8),
          a.val = bytes.val.take 1 ∧ t.val = bytes.val.drop 1 ∧
          r = .Ok (Aeneas.Std.core.num.U8.from_be_bytes a, t)) ∧
        (bytes.val.length < 1 → r = .Err Error.EndOfStream))
    (hcf : core.ops.control_flow.ControlFlow.Continue p = tryCF r) :
    ∃ l, bytes.val = p.1 :: l ∧ p.2.val = l := by
  rw [continue_eq_tryCF] at hcf
  have hl : 1 ≤ bytes.val.length := by
    by_contra hn
    rw [hP.2 (by omega)] at hcf
    cases hcf
  obtain ⟨a, t, ha, ht, hr⟩ := hP.1 hl
  rw [hr, core.result.Result.Ok.injEq] at hcf
  subst hcf
  cases hb : bytes.val with
  | nil => rw [hb] at hl; simp at hl
  | cons b l =>
    rw [hb] at ha ht
    simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero] at ha ht
    refine ⟨l, ?_, ht⟩
    simp only [U8_from_be_bytes_of_val a b ha]

/-- A `Break` of `?` on the result of `u8::tls_deserialize_bytes` means the input was empty. -/
theorem U8_deserialize_err {bytes : Slice Std.U8} {r : core.result.Result (Std.U8 × Slice Std.U8) Error}
    {res : core.result.Result core.convert.Infallible Error}
    (hP : (1 ≤ bytes.val.length → ∃ (a : Aeneas.Std.Array Std.U8 1#usize) (t : Slice Std.U8),
          a.val = bytes.val.take 1 ∧ t.val = bytes.val.drop 1 ∧
          r = .Ok (Aeneas.Std.core.num.U8.from_be_bytes a, t)) ∧
        (bytes.val.length < 1 → r = .Err Error.EndOfStream))
    (hcf : core.ops.control_flow.ControlFlow.Break res = tryCF r) :
    bytes.val = [] := by
  by_contra hne
  have hl : 1 ≤ bytes.val.length := by
    cases hb : bytes.val with
    | nil => exact absurd hb hne
    | cons b l => simp
  obtain ⟨a, t, ha, ht, hr⟩ := hP.1 hl
  rw [hr] at hcf
  simp only [tryCF, reduceCtorEq] at hcf

/-- Consequences of a successful `?` on the result of `u16::tls_deserialize_bytes`. -/
theorem U16_deserialize_ok {s : Slice Std.U8} {r : core.result.Result (Std.U16 × Slice Std.U8) Error}
    {p : Std.U16 × Slice Std.U8}
    (hP : (2 ≤ s.val.length → ∃ (a : Aeneas.Std.Array Std.U8 2#usize) (t : Slice Std.U8),
          a.val = s.val.take 2 ∧ t.val = s.val.drop 2 ∧
          r = .Ok (Aeneas.Std.core.num.U16.from_be_bytes a, t)) ∧
        (s.val.length < 2 → r = .Err Error.EndOfStream))
    (hcf : core.ops.control_flow.ControlFlow.Continue p = tryCF r) :
    2 ≤ s.val.length ∧ ∃ (a : Aeneas.Std.Array Std.U8 2#usize) (t : Slice Std.U8),
      a.val = s.val.take 2 ∧ t.val = s.val.drop 2 ∧ p = (Aeneas.Std.core.num.U16.from_be_bytes a, t) := by
  rw [continue_eq_tryCF] at hcf
  have hl : 2 ≤ s.val.length := by
    by_contra hn
    rw [hP.2 (by omega)] at hcf
    cases hcf
  obtain ⟨a, t, ha, ht, hr⟩ := hP.1 hl
  rw [hr, core.result.Result.Ok.injEq] at hcf
  exact ⟨hl, a, t, ha, ht, hcf.symm⟩

/-- A `Break` of `?` on the result of `u16::tls_deserialize_bytes` means the input was too short. -/
theorem U16_deserialize_err {s : Slice Std.U8} {r : core.result.Result (Std.U16 × Slice Std.U8) Error}
    {res : core.result.Result core.convert.Infallible Error}
    (hP : (2 ≤ s.val.length → ∃ (a : Aeneas.Std.Array Std.U8 2#usize) (t : Slice Std.U8),
          a.val = s.val.take 2 ∧ t.val = s.val.drop 2 ∧
          r = .Ok (Aeneas.Std.core.num.U16.from_be_bytes a, t)) ∧
        (s.val.length < 2 → r = .Err Error.EndOfStream))
    (hcf : core.ops.control_flow.ControlFlow.Break res = tryCF r) :
    s.val.length < 2 := by
  by_contra hn
  obtain ⟨a, t, ha, ht, hr⟩ := hP.1 (by omega)
  rw [hr] at hcf
  simp only [tryCF, reduceCtorEq] at hcf

/-- Exact behaviour of `Option<u16>::tls_deserialize_bytes`. -/
theorem Option_U16_deserialize_char (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ core.option.Option.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes
      U16.Insts.Tls_codecDeserializeBytes bytes
    ⦃ ⇓ r => ⌜ (∀ l, bytes.val = 0#u8 :: l → ∃ t : Slice Std.U8, t.val = l ∧ r = .Ok (.none, t)) ∧
        (∀ l, bytes.val = 1#u8 :: l → 2 ≤ l.length →
          ∃ (a : Aeneas.Std.Array Std.U8 2#usize) (t : Slice Std.U8), a.val = l.take 2 ∧
            t.val = l.drop 2 ∧
            r = .Ok (.some (Aeneas.Std.core.num.U16.from_be_bytes a), t)) ∧
        (∀ v t, r = .Ok (v, t) →
          (∃ l, bytes.val = 0#u8 :: l ∧ v = .none ∧ t.val = l) ∨
          (∃ (a : Aeneas.Std.Array Std.U8 2#usize) (l : List Std.U8), bytes.val = 1#u8 :: (a.val ++ l) ∧
            v = .some (Aeneas.Std.core.num.U16.from_be_bytes a) ∧ t.val = l)) ⌝ ⦄ := by
  mvcgen [core.option.Option.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes,
    U8_deserialize_char, U16_deserialize_char]
  · rename_i r1 hP cf p hx hz hcf
    obtain ⟨l, hb, hp2⟩ := U8_deserialize_ok hP hcf
    rw [hz] at hb
    refine ⟨fun l' hl' => ?_, fun l' hl' _ => ?_, fun v t hv => ?_⟩
    · rw [hb] at hl'
      have := (List.cons.inj hl').2
      exact ⟨p.2, by rw [hp2, this], rfl⟩
    · rw [hb] at hl'
      exact absurd (List.cons.inj hl').1 (by decide)
    · simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at hv
      obtain ⟨hv1, hv2⟩ := hv
      subst hv1 hv2
      exact Or.inl ⟨l, hb, rfl, hp2⟩
  · rename_i r1 hP cf p hx hz hcf r2 hP2 cf2 p2 hx2 hcf2
    obtain ⟨l, hb, hp2⟩ := U8_deserialize_ok hP hcf
    obtain ⟨hl2, a, t, ha, ht, hp⟩ := U16_deserialize_ok hP2 hcf2
    rw [hz] at hb
    subst hp
    refine ⟨fun l' hl' => ?_, fun l' hl' hl2' => ?_, fun v t' hv => ?_⟩
    · rw [hb] at hl'
      exact absurd (List.cons.inj hl').1 (by decide)
    · rw [hb] at hl'
      have hll := (List.cons.inj hl').2
      subst hll
      rw [hp2] at ha ht
      exact ⟨a, t, ha, ht, rfl⟩
    · simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at hv
      obtain ⟨hv1, hv2⟩ := hv
      subst hv1 hv2
      refine Or.inr ⟨a, l.drop 2, ?_, rfl, ?_⟩
      · rw [hb, ha, hp2, List.take_append_drop]
        rfl
      · rw [ht, hp2]
  · rename_i r1 hP cf p hx hz hcf r2 hP2 cf2 resid hx2
    obtain ⟨l, hb, hp2⟩ := U8_deserialize_ok hP hcf
    rw [hz] at hb
    apply try_break_vc
    intro e he
    mvcgen
    intro hre
    subst hre
    simp only [PostCond.ok]
    refine ⟨fun l' hl' => ?_, fun l' hl' hl2' => ?_, fun v t hv => ?_⟩
    · rw [hb] at hl'
      exact absurd (List.cons.inj hl').1 (by decide)
    · rw [hb] at hl'
      have hll := (List.cons.inj hl').2
      subst hll
      rw [hp2] at hP2
      obtain ⟨a, t, _, _, hr⟩ := hP2.1 hl2'
      rw [he] at hr
      cases hr
    · cases hv
  · rename_i r1 hP cf p hx n h0 h1 hn hcf a1 a2 s1 s2 hs
    obtain ⟨l, hb, hp2⟩ := U8_deserialize_ok hP hcf
    refine ⟨fun l' hl' => ?_, fun l' hl' _ => ?_, fun v t hv => ?_⟩
    · rw [hb, hn] at hl'
      exact absurd (List.cons.inj hl').1 h0
    · rw [hb, hn] at hl'
      exact absurd (List.cons.inj hl').1 h1
    · cases hv
  · rename_i r1 hP cf resid hx
    apply try_break_vc
    intro e he
    mvcgen
    intro hre
    subst hre
    simp only [PostCond.ok]
    have hlen : bytes.val.length < 1 := by
      by_contra hn
      obtain ⟨a, t, _, _, hr⟩ := hP.1 (by omega)
      rw [he] at hr
      cases hr
    refine ⟨fun l' hl' => ?_, fun l' hl' hl2' => ?_, fun v t hv => ?_⟩
    · rw [hl'] at hlen; simp at hlen
    · rw [hl'] at hlen; simp at hlen
    · cases hv

/-! ### `copy_from_slice` -/

/-- Cloning a `u8` list is the identity. -/
theorem mapM_clone_U8 (l : List Std.U8) :
    l.mapM core.U8.Insts.CoreCloneClone.clone = ok l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, ih]
    rfl

/-- `dest.copy_from_slice(src)` on `u8`: if it returns, the lengths agree and the result is `src`.
Partial: it panics when the lengths differ. -/
theorem core.slice.Slice.copy_from_slice_U8_spec (s src : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ core.slice.Slice.copy_from_slice core.U8.Insts.CoreMarkerCopy s src
    ⦃ ⇓? r => ⌜ s.val.length = src.val.length ∧ r.val = src.val ⌝ ⦄ := by
  apply partial_triple_of_ok
  intro r hr
  unfold core.slice.Slice.copy_from_slice rust_primitives.slice.slice_clone_from_slice at hr
  split at hr
  · rename_i hlen
    split at hr
    · rename_i cloned hcl
      rw [mapM_clone_U8] at hcl
      have : src.val = cloned := by injection hcl
      cases hr
      exact ⟨hlen, this.symm⟩
    · rename_i e hcl
      rw [mapM_clone_U8] at hcl
      cases hcl
    · rename_i hcl
      rw [mapM_clone_U8] at hcl
      cases hcl
  · cases hr

/-- Total version of `copy_from_slice_U8_spec`: with equal lengths, the call does not panic.
Not tagged `@[spec]` (extra hypothesis). -/
theorem core.slice.Slice.copy_from_slice_U8_total (s src : Slice Std.U8)
    (h : s.val.length = src.val.length) :
    ⦃ ⌜ True ⌝ ⦄ core.slice.Slice.copy_from_slice core.U8.Insts.CoreMarkerCopy s src
    ⦃ ⇓ r => ⌜ r.val = src.val ⌝ ⦄ := by
  unfold core.slice.Slice.copy_from_slice rust_primitives.slice.slice_clone_from_slice
  rw [if_pos h]
  split
  · rename_i cloned hcl
    rw [mapM_clone_U8] at hcl
    have : src.val = cloned := by injection hcl
    apply RustM.ok_spec
    exact this.symm
  · rename_i e hcl
    rw [mapM_clone_U8] at hcl
    cases hcl
  · rename_i hcl
    rw [mapM_clone_U8] at hcl
    cases hcl

/-- `size_of::<usize>()` returns `numBits / 8`. -/
theorem core.mem.size_of_Usize_spec :
    ⦃ ⌜ True ⌝ ⦄ core.mem.size_of Std.Usize
    ⦃ ⇓ n => ⌜ n.val * 8 = System.Platform.numBits ⌝ ⦄ := by
  obtain ⟨n, hn, h8⟩ := core.mem.size_of_Usize
  rw [hn]
  mvcgen

/-! ### `usize::from_be_bytes` of a `U24` -/

/-- One step of `BitVec.fromLEBytes`, on the value. -/
theorem setWidth_or_shift_toNat {n w : Nat} (h : w = n + 8) (b : BitVec 8) (x : BitVec n) :
    (BitVec.setWidth w b ||| BitVec.setWidth w x <<< 8).toNat = b.toNat + 256 * x.toNat := by
  subst h
  have hb := b.isLt
  have hx := x.isLt
  have hpow : 2 ^ (n + 8) = 2 ^ n * 256 := by rw [Nat.pow_add]
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have h1 : b.toNat % 2 ^ (n + 8) = b.toNat := Nat.mod_eq_of_lt (by
    have : 256 ≤ 2 ^ (n + 8) := by rw [hpow]; have : 1 ≤ 2 ^ n := Nat.one_le_two_pow; omega
    omega)
  have h2 : x.toNat % 2 ^ (n + 8) = x.toNat := Nat.mod_eq_of_lt (by omega)
  have h3 : (x.toNat <<< 8) % 2 ^ (n + 8) = x.toNat <<< 8 := Nat.mod_eq_of_lt (by
    rw [Nat.shiftLeft_eq]; omega)
  rw [h1, h2, h3, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by omega) x.toNat, Nat.shiftLeft_eq]
  omega

/-- Value of a little-endian byte string. -/
theorem fromLEBytes_toNat : ∀ (l : List (BitVec 8)),
    (BitVec.fromLEBytes l).toNat = l.foldr (fun b acc => b.toNat + 256 * acc) 0
  | [] => by simp [BitVec.fromLEBytes.eq_1]
  | b :: t => by
    rw [BitVec.fromLEBytes.eq_2, setWidth_or_shift_toNat (by simp; omega), fromLEBytes_toNat t]
    rfl

/-- Value of eight big-endian bytes whose first five are zero. -/
theorem fromBEBytes_zero5_toNat (b0 b1 b2 : BitVec 8) :
    (BitVec.fromBEBytes [0#8, 0#8, 0#8, 0#8, 0#8, b0, b1, b2]).toNat =
      b0.toNat * 65536 + b1.toNat * 256 + b2.toNat := by
  unfold BitVec.fromBEBytes
  rw [BitVec.toNat_cast, fromLEBytes_toNat]
  simp [List.foldr]
  omega

/-- The `usize` read back from `[0,0,0,0,0,b0,b1,b2]` (64-bit platform). -/
theorem usize_from_zero5_val (b0 b1 b2 : Std.U8) (h64 : System.Platform.numBits = 64) :
    (UScalar.mk (ty := UScalarTy.Usize) (BitVec.setWidth UScalarTy.Usize.numBits
      (BitVec.fromBEBytes (List.map U8.bv [0#u8, 0#u8, 0#u8, 0#u8, 0#u8, b0, b1, b2])))).val =
      b0.val * 65536 + b1.val * 256 + b2.val := by
  have hb0 : b0.bv.toNat < 256 := b0.bv.isLt
  have hb1 : b1.bv.toNat < 256 := b1.bv.isLt
  have hb2 : b2.bv.toNat < 256 := b2.bv.isLt
  have h1 := fromBEBytes_zero5_toNat b0.bv b1.bv b2.bv
  have hnb : UScalarTy.Usize.numBits = 64 := h64
  show (BitVec.setWidth UScalarTy.Usize.numBits
      (BitVec.fromBEBytes (List.map U8.bv [0#u8, 0#u8, 0#u8, 0#u8, 0#u8, b0, b1, b2]))).toNat =
    b0.bv.toNat * 65536 + b1.bv.toNat * 256 + b2.bv.toNat
  rw [BitVec.toNat_setWidth, hnb]
  have h2 : (BitVec.fromBEBytes (List.map U8.bv [0#u8, 0#u8, 0#u8, 0#u8, 0#u8, b0, b1, b2])).toNat =
      b0.bv.toNat * 65536 + b1.bv.toNat * 256 + b2.bv.toNat := h1
  rw [h2]
  apply Nat.mod_eq_of_lt
  omega

/-! ### `TlsVarInt::tls_deserialize_bytes` -/

/-- `calculate_value` never fails: `Ok (v, len)` with `v < 64` and `len` one of `1, 2, 4, 8`. -/
theorem varint.calculate_value_char (byte : Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ varint.calculate_value byte
    ⦃ ⇓ r => ⌜ ∃ v l : Std.Usize, r = .Ok (v, l) ∧ v.val < 64 ∧
        (l.val = 1 ∨ l.val = 2 ∨ l.val = 4 ∨ l.val = 8) ⌝ ⦄ := by
  have := System.Platform.numBits_eq
  have hand : (byte &&& 63#u8).val < 64 := by
    have h := Nat.and_le_right (n := byte.val) (m := 63)
    have : (byte &&& 63#u8).val = byte.val &&& 63 := by simp
    omega
  mvcgen [varint.calculate_value, varint.TlsVarInt.MAX_LOG]
  · exfalso; scalar_tac
  · exact ⟨_, _, rfl, by scalar_tac, by simp⟩
  · exact ⟨_, _, rfl, by scalar_tac, by simp⟩
  · exact ⟨_, _, rfl, by scalar_tac, by simp⟩
  · exact ⟨_, _, rfl, by scalar_tac, by simp⟩
  · exfalso; scalar_tac
  · exfalso; scalar_tac

/-- Arithmetic of one step `value ← (value << 8) + byte` of the varint decoder. -/
theorem varint.step_bound (v b i : Nat) (hi : 1 ≤ i) (hi8 : i + 1 ≤ 8) (hv : v < 2 ^ (8 * i - 2))
    (hb : b < 256) :
    (v <<< 8) % 2 ^ 64 = v * 256 ∧ v * 256 + b < 2 ^ (8 * (i + 1) - 2) ∧ v * 256 + b < 2 ^ 64 := by
  have e : 2 ^ (8 * (i + 1) - 2) = 2 ^ (8 * i - 2) * 256 := by
    have : 8 * (i + 1) - 2 = (8 * i - 2) + 8 := by omega
    rw [this, Nat.pow_add]
  have hle : 2 ^ (8 * (i + 1) - 2) ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsh : v <<< 8 = v * 256 := by rw [Nat.shiftLeft_eq]
  have hlt : v * 256 + b < 2 ^ (8 * (i + 1) - 2) := by rw [e]; omega
  have h62 : (2:Nat) ^ 62 < 2 ^ 64 := by norm_num
  have hlt64 : v * 256 + b < 2 ^ 64 := Nat.lt_of_lt_of_le hlt (le_trans hle h62.le)
  refine ⟨?_, hlt, hlt64⟩
  rw [hsh]; apply Nat.mod_eq_of_lt; exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hlt64

/-- `u64::from(u8)` is the widening cast. -/
@[spec] theorem core.U64.Insts.CoreConvertFromU8.from_spec (x : Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ core.U64.Insts.CoreConvertFromU8.from x
    ⦃ ⇓ r => ⌜ r.val = x.val ⌝ ⦄ := by
  unfold core.U64.Insts.CoreConvertFromU8.from; mvcgen

/-- One iteration of the `TlsVarInt::tls_deserialize_bytes` loop. -/
theorem varint.deserialize_loop.body_spec (len : Std.Usize) (remainder : Slice Std.U8)
    (value : Std.U64) (i : Std.Usize) (hi : 1 ≤ i.val) (hil : i.val ≤ len.val) (hl : len.val ≤ 8)
    (hv : value.val < 2 ^ (8 * i.val - 2)) :
    ⦃ ⌜ True ⌝ ⦄
    varint.TlsVarInt.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes_loop.body len remainder value i
    ⦃ ⇓ r => ⌜ match r with
      | .done (r', v', f) => (f = core.option.Option.None → i = len ∧ r' = remainder ∧ v' = value)
      | .cont (r', v', i') => r'.val.length + 1 = remainder.val.length ∧ i'.val = i.val + 1 ∧
          i'.val ≤ len.val ∧ v'.val < 2 ^ (8 * i'.val - 2) ⌝ ⦄ := by
  unfold varint.TlsVarInt.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes_loop.body
  mvcgen [U8_deserialize_char]
  · rename_i hlt r0 p hr hP r3 h3 h3b h3c r2 h2 r1 h1 r h0
    have hb := varint.step_bound value.val r2.val i.val hi (by scalar_tac) hv (by scalar_tac)
    have hrl : 1 ≤ remainder.val.length := by
      by_contra hn
      have := hP.2 (by omega)
      cases this
    obtain ⟨a, t, ha, ht, hpt⟩ := hP.1 hrl
    have hp2 : p.2 = t := (congrArg Prod.snd (core.result.Result.Ok.inj hpt)).trans rfl
    rw [hp2, ht]
    simp only [List.length_drop]
    have h1' : (1#usize).val = 1 := by simp
    refine ⟨by omega, by scalar_tac, by scalar_tac, ?_⟩
    have : r.val = i.val + 1 := by scalar_tac
    rw [this]
    scalar_tac
  · rename_i hlt r0 p hr hP r3 h3 h3b h3c r2 h2 r1 h1 hov
    exfalso
    have hb := varint.step_bound value.val r2.val i.val hi (by scalar_tac) hv (by scalar_tac)
    scalar_tac
  · rename_i hlt r0 p hr hP r3 h3 h3b h3c r2 h2 hov
    exfalso
    have hb := varint.step_bound value.val r2.val i.val hi (by scalar_tac) hv (by scalar_tac)
    scalar_tac
  · intro h; cases h
  · apply UScalar.eq_of_val_eq; scalar_tac

/-- The `TlsVarInt::tls_deserialize_bytes` loop: it never panics; without failure it consumes
`len - i` bytes and the value stays below `2^(8*len-2)`. -/
theorem varint.deserialize_loop_spec (remainder : Slice Std.U8) (len : Std.Usize) (value : Std.U64)
    (i : Std.Usize) (hi : 1 ≤ i.val) (hil : i.val ≤ len.val) (hl : len.val ≤ 8)
    (hv : value.val < 2 ^ (8 * i.val - 2)) :
    ⦃ ⌜ True ⌝ ⦄
    varint.TlsVarInt.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes_loop remainder len value i
    ⦃ ⇓ r => ⌜ r.2.2 = core.option.Option.None →
        r.1.val.length + len.val = remainder.val.length + i.val ∧
        r.2.1.val < 2 ^ (8 * len.val - 2) ⌝ ⦄ := by
  unfold varint.TlsVarInt.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes_loop
  apply Aeneas.Std.WP.spec_to_mvcgen
  apply Aeneas.Std.loop.spec_decr_nat
    (fun x : Slice Std.U8 × Std.U64 × Std.Usize => len.val - x.2.2.val)
    (fun x : Slice Std.U8 × Std.U64 × Std.Usize =>
      1 ≤ x.2.2.val ∧ x.2.2.val ≤ len.val ∧ x.2.1.val < 2 ^ (8 * x.2.2.val - 2) ∧
      x.1.val.length + x.2.2.val = remainder.val.length + i.val)
    (fun y : Slice Std.U8 × Std.U64 × (core.option.Option Error) => y.2.2 = core.option.Option.None →
        y.1.val.length + len.val = remainder.val.length + i.val ∧
        y.2.1.val < 2 ^ (8 * len.val - 2))
  · rintro ⟨b, v, j⟩ ⟨hj1, hjl, hjv, hjr⟩
    dsimp only at hj1 hjl hjv hjr
    obtain ⟨r, hr, hP⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp
      (varint.deserialize_loop.body_spec len b v j hj1 hjl hl hjv)
    dsimp only
    rw [hr, Aeneas.Std.WP.spec_ok]
    cases r with
    | done y =>
      obtain ⟨r', v', f⟩ := y
      intro hf
      obtain ⟨h1, h2, h3⟩ := hP hf
      subst h2; subst h3
      have : j.val = len.val := by rw [h1]
      dsimp only at hjv hjr ⊢
      refine ⟨by omega, ?_⟩
      rw [← this]; exact hjv
    | cont x =>
      obtain ⟨b', v', j'⟩ := x
      obtain ⟨h1, h2, h3, h4⟩ := hP
      dsimp only at h1 h2 h3 h4 ⊢
      refine ⟨⟨by omega, h3, h4, by omega⟩, by omega⟩
  · exact ⟨hi, hil, hv, rfl⟩

/-- `check_min_len` succeeds iff the value is at most `MAX` and the length is the minimal one. -/
theorem varint.check_min_len_char (value : Std.U64) (len : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ varint.check_min_len value len
    ⦃ ⇓ r => ⌜ r = .Ok () → value.val ≤ 2 ^ 62 - 1 ∧ len.val = varint.lenOf value.val ⌝ ⦄ := by
  mvcgen [varint.check_min_len]
  · intro h; cases h
  · rename_i r2 hr2 cf val1 hx hcf r hne hr
    rw [continue_eq_tryCF] at hcf
    rw [hcf] at hr2
    obtain ⟨hv1, hle⟩ := hr2
    subst hv1
    have hc := varint.lenOf_char _ _ hr
    have hrl : r.val = len.val := by simpa using hne
    exact ⟨hle, by rw [← hrl]; exact hc.1⟩
  · try_vcs
    intro _ h; cases h

/-- A successful `u8::tls_deserialize_bytes` consumes exactly one byte. -/
theorem U8_deserialize_len {bytes : Slice Std.U8} {r : core.result.Result (Std.U8 × Slice Std.U8) Error}
    {p : Std.U8 × Slice Std.U8}
    (hP : (1 ≤ bytes.val.length → ∃ (a : Aeneas.Std.Array Std.U8 1#usize) (t : Slice Std.U8),
          a.val = bytes.val.take 1 ∧ t.val = bytes.val.drop 1 ∧
          r = .Ok (Aeneas.Std.core.num.U8.from_be_bytes a, t)) ∧
        (bytes.val.length < 1 → r = .Err Error.EndOfStream))
    (h : r = .Ok p) : bytes.val.length = p.2.val.length + 1 := by
  have hl : 1 ≤ bytes.val.length := by
    by_contra hn
    rw [hP.2 (by omega)] at h
    cases h
  obtain ⟨a, t, _, ht, hr⟩ := hP.1 hl
  rw [hr] at h
  have h2 := congrArg Prod.snd (core.result.Result.Ok.inj h)
  simp only at h2
  rw [← h2, ht]
  simp only [List.length_drop]
  omega

/-- Facts about the `Ok` result of `calculate_value_char`. -/
theorem varint.calculate_value_ok {r : core.result.Result (Std.Usize × Std.Usize) Error}
    {val : Std.Usize × Std.Usize}
    (hvl : ∃ v l : Std.Usize, r = .Ok (v, l) ∧ v.val < 64 ∧
        (l.val = 1 ∨ l.val = 2 ∨ l.val = 4 ∨ l.val = 8))
    (h : r = .Ok val) :
    val.1.val < 64 ∧ 1 ≤ val.2.val ∧ val.2.val ≤ 8 := by
  obtain ⟨v, l, h1, h2, h3⟩ := hvl
  rw [h1] at h
  have := core.result.Result.Ok.inj h
  subst this
  refine ⟨h2, ?_, ?_⟩ <;> simp only <;> omega

/-- `TlsVarInt::tls_deserialize_bytes` never panics; on success the value is at most `MAX` and the
remainder is the input minus the minimal encoding of the value. -/
theorem varint.TlsVarInt.deserialize_char (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ varint.TlsVarInt.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : varint.TlsVarInt) (t : Slice Std.U8), r = .Ok (v, t) →
        v.val ≤ 2 ^ 62 - 1 ∧ t.val.length + varint.lenOf v.val = bytes.val.length ⌝ ⦄ := by
  mvcgen [varint.TlsVarInt.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes,
    U8_deserialize_char, varint.calculate_value_char, varint.check_min_len_char,
    varint.deserialize_loop_spec, core.result.Result.map_err_spec,
    varint.DeserializeBytesTlsVarInt.tls_deserialize_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError.call_once]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  · rename_i r0 hP r1 p x1 r2 hvl r3 val x2 r4 hcast t ha r5 val1 x3 hr0 hr2 hr4
    have := varint.calculate_value_ok hvl hr2
    scalar_tac
  · rename_i r0 hP r1 p x1 r2 hvl r3 val x2 r4 hcast t ha r5 val1 x3 hr0 hr2 hr4
    have := varint.calculate_value_ok hvl hr2
    scalar_tac
  · rename_i r0 hP r1 p x1 r2 hvl r3 val x2 r4 hcast t ha r5 val1 x3 hr0 hr2 hr4
    have h64 := (varint.calculate_value_ok hvl hr2).1
    rw [hcast] at ha
    have ht := core.result.Result.Ok.inj ha
    have hv1 := core.result.Result.Ok.inj hr4
    subst hv1; subst ht
    scalar_tac
  · rename_i r0 hP r1 p x1 r2 hvl r3 val x2 r4 hcast t ha r5 val1 x3 rl xn hloop r6 hchk r7 u x4 hr0 hr2 hr4 hr6
    intro v t' hvt
    have hvt' := core.result.Result.Ok.inj hvt
    have hc := hchk hr6
    have hlp := (hloop xn).1
    have hb := U8_deserialize_len hP hr0
    obtain ⟨hv, ht⟩ := Prod.mk.inj hvt'
    subst hv; subst ht
    have h1 : (1#usize).val = 1 := by simp
    refine ⟨hc.1, ?_⟩
    rw [← hc.2]
    omega
  · intro _ v t h; cases h
  · intro v t h; cases h
  · rename_i r0 hP r1 p x1 r2 hvl r3 val x2 r4 hcast e ha hr0 hr2
    exfalso
    rw [hcast] at ha
    cases ha
  · intro _ v t h; cases h
  · intro _ v t h; cases h

/-- `ContentLength::tls_deserialize_bytes` never panics; on success the value is at most `2^30 - 1`
(RFC 9420 2.1.2) and the remainder is the input minus the minimal varint encoding of the value. -/
theorem quic_vec.ContentLength.deserialize_char (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ quic_vec.ContentLength.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : quic_vec.ContentLength) (t : Slice Std.U8), r = .Ok (v, t) →
        v.val ≤ 2 ^ 30 - 1 ∧ t.val.length + varint.lenOf v.val = bytes.val.length ⌝ ⦄ := by
  mvcgen [quic_vec.ContentLength.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes,
    varint.TlsVarInt.deserialize_char, quic_vec.ContentLength.new, varint.TlsVarInt.value,
    quic_vec.ContentLength.MAX, quic_vec.MAX_MLS_LEN_spec]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  · intro _ v t h; cases h
  · rename_i r0 hP r1 p x1 r2 h2 h1 r3 val x2 hr0 hval
    have hv := core.result.Result.Ok.inj hval
    have hb : p.1.val ≤ 2 ^ 30 - 1 := by scalar_tac
    subst hv
    intro v t hvt
    obtain ⟨hv1, ht⟩ := Prod.mk.inj (core.result.Result.Ok.inj hvt)
    subst hv1; subst ht
    exact ⟨hb, (hP p.1 p.2 hr0).2⟩
  · intro _ v t h; cases h

/-- `tls_serialize_bytes_len` of a slice of length at most `2^30 - 1` (the MLS bound) is the length
plus the minimal varint length prefix. -/
theorem quic_vec.tls_serialize_bytes_len_char (bytes : Slice Std.U8)
    (h : bytes.val.length ≤ 2 ^ 30 - 1) :
    ⦃ ⌜ True ⌝ ⦄ quic_vec.tls_serialize_bytes_len bytes
    ⦃ ⇓ r => ⌜ r.val = bytes.val.length + varint.lenOf bytes.val.length ⌝ ⦄ := by
  mvcgen [quic_vec.tls_serialize_bytes_len, CoreModels.core.slice.Slice.len_spec]
  · rename_i n hn rc hrc r2 hr2 r1 hr1 r3 hr3
    have hl : n.val = bytes.val.length := by subst hn; simp [Slice.len]
    cases rc with
    | Ok c =>
      obtain ⟨hc, _⟩ := hrc
      obtain ⟨u, hu, _, _, hul⟩ := hr2.1 c rfl
      subst hu
      simp only at hr1
      subst hr1
      rw [hul] at hr3
      have hcl : c.val = bytes.val.length := by omega
      rw [← hcl]
      scalar_tac
    | Err e => omega
  · rename_i n hn rc hrc r2 hr2 r1 hr1 hov
    have hl : n.val = bytes.val.length := by subst hn; simp [Slice.len]
    cases rc with
    | Ok c =>
      obtain ⟨hc, _⟩ := hrc
      obtain ⟨u, hu, h1, h8, hul⟩ := hr2.1 c rfl
      subst hu
      simp only at hr1
      subst hr1
      scalar_tac
    | Err e => omega

/-- `VLBytes::tls_deserialize_bytes` never panics; on success the payload is at most `2^30 - 1` bytes
and the remainder is the input minus the varint length prefix and the payload. -/
theorem quic_vec.VLBytes.deserialize_char (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ quic_vec.VLBytes.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : quic_vec.VLBytes) (t : Slice Std.U8), r = .Ok (v, t) →
        v.vec.val.length ≤ 2 ^ 30 - 1 ∧
        t.val.length + (v.vec.val.length + varint.lenOf v.vec.val.length) = bytes.val.length ⌝ ⦄ := by
  mvcgen [quic_vec.VLBytes.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes,
    quic_vec.ContentLength.deserialize_char, varint.TlsVarInt.value, quic_vec.VLBytes.new,
    core.option.Option.ok_or_spec, core.Slice.Insts.CoreOpsIndexIndex.index_spec,
    alloc.vec.Vec.new_spec, core.hint.must_use_spec]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  · rename_i r0 hP r1 p x1 r2 htf r3 val x2 hv0 rv hrv h3 h5
    intro v t h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (core.result.Result.Ok.inj h)
    have hl := (hP p.1 p.2 h3).2
    have hy := htf.1 val h5
    have hv : val.val = 0 := by rw [hv0]; rfl
    have hrl : rv.val.length = 0 := by rw [hrv]; simp [Slice.new]
    have hlen : varint.lenOf p.1.val = 1 := by
      have : p.1.val = 0 := by omega
      rw [this]; simp [varint.lenOf]
    refine ⟨by simp only; omega, ?_⟩
    simp only
    rw [hrl]
    have h0 : varint.lenOf 0 = 1 := by simp [varint.lenOf]
    omega
  · rename_i r0 hP r1 p x1 r2 htf r3 val x2 hv0 o ho rr vec hrr hok rv hrv ro h3 h5
    intro hd hn
    have hb := (hP p.1 p.2 h3)
    have hy := htf.1 val h5
    have hvl : val.val ≤ p.2.val.length := by
      by_contra hc
      rw [ho.2 (by omega)] at hok
      cases hok
    obtain ⟨t, ht, ht'⟩ := ho.1 hvl
    rw [ht] at hok
    have hvec := core.result.Result.Ok.inj hok.symm
    obtain ⟨t2, h2, h2'⟩ := hd hvl
    refine ⟨t2, h2, ?_⟩
    simp only [PostCond.ok]
    mvcgen
    intro v t h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (core.result.Result.Ok.inj h)
    have hrl : rv.val.length = val.val := by
      rw [hrv, ← hvec, ht']; simp only [List.length_take]; omega
    have hl2 : t2.val.length = p.2.val.length - val.val := by rw [h2']; simp
    show rv.val.length ≤ 2 ^ 30 - 1 ∧
      t2.val.length + (rv.val.length + varint.lenOf rv.val.length) = bytes.val.length
    rw [hrl, hl2, hy]
    refine ⟨by omega, ?_⟩
    omega
  · intro v t h; cases h
  · exfalso
    rename_i r0 hP r1 p x1 r2 htf r3 residual x2 e hr2 h3
    have hb := (hP p.1 p.2 h3)
    obtain ⟨y, hy⟩ := htf.2 (by omega)
    rw [hy] at hr2
    cases hr2
  · intro _ v t h; cases h

/-- `VLBytes::tls_serialized_len` of a payload of at most `2^30 - 1` bytes is the payload length plus
the minimal varint length prefix. -/
theorem quic_vec.VLBytes.serialized_len_char (self : quic_vec.VLBytes)
    (h : self.vec.val.length ≤ 2 ^ 30 - 1) :
    ⦃ ⌜ True ⌝ ⦄ quic_vec.VLBytes.Insts.Tls_codecSize.tls_serialized_len self
    ⦃ ⇓ r => ⌜ r.val = self.vec.val.length + varint.lenOf self.vec.val.length ⌝ ⦄ := by
  mvcgen [quic_vec.VLBytes.Insts.Tls_codecSize.tls_serialized_len, quic_vec.VLBytes.as_slice,
    quic_vec.VLBytes.impl.vec, quic_vec.tls_serialize_bytes_len_char]
  · intro hr; subst_vars; exact hr
  · intro hr; subst_vars; exact h

/-- `VLByteVec::tls_deserialize_bytes` never panics; on success the payload is at most `2^30 - 1` bytes
and the remainder is the input minus the varint length prefix and the payload. -/
theorem quic_vec.VLByteVec.deserialize_char (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ quic_vec.VLByteVec.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : quic_vec.VLByteVec) (t : Slice Std.U8), r = .Ok (v, t) →
        v.vec.val.length ≤ 2 ^ 30 - 1 ∧
        t.val.length + (v.vec.val.length + varint.lenOf v.vec.val.length) = bytes.val.length ⌝ ⦄ := by
  mvcgen [quic_vec.VLByteVec.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes,
    quic_vec.ContentLength.deserialize_char, varint.TlsVarInt.value, quic_vec.VLByteVec.new,
    core.option.Option.ok_or_spec, core.Slice.Insts.CoreOpsIndexIndex.index_spec,
    alloc.vec.Vec.new_spec, core.hint.must_use_spec]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  · rename_i r0 hP r1 p x1 r2 htf r3 val x2 hv0 rv hrv h3 h5
    intro v t h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (core.result.Result.Ok.inj h)
    have hl := (hP p.1 p.2 h3).2
    have hy := htf.1 val h5
    have hv : val.val = 0 := by rw [hv0]; rfl
    have hrl : rv.val.length = 0 := by rw [hrv]; simp [Slice.new]
    have hlen : varint.lenOf p.1.val = 1 := by
      have : p.1.val = 0 := by omega
      rw [this]; simp [varint.lenOf]
    refine ⟨by simp only; omega, ?_⟩
    simp only
    rw [hrl]
    have h0 : varint.lenOf 0 = 1 := by simp [varint.lenOf]
    omega
  · rename_i r0 hP r1 p x1 r2 htf r3 val x2 hv0 o ho rr vec hrr hok rv hrv ro h3 h5
    intro hd hn
    have hb := (hP p.1 p.2 h3)
    have hy := htf.1 val h5
    have hvl : val.val ≤ p.2.val.length := by
      by_contra hc
      rw [ho.2 (by omega)] at hok
      cases hok
    obtain ⟨t, ht, ht'⟩ := ho.1 hvl
    rw [ht] at hok
    have hvec := core.result.Result.Ok.inj hok.symm
    obtain ⟨t2, h2, h2'⟩ := hd hvl
    refine ⟨t2, h2, ?_⟩
    simp only [PostCond.ok]
    mvcgen
    intro v t h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (core.result.Result.Ok.inj h)
    have hrl : rv.val.length = val.val := by
      rw [hrv, ← hvec, ht']; simp only [List.length_take]; omega
    have hl2 : t2.val.length = p.2.val.length - val.val := by rw [h2']; simp
    show rv.val.length ≤ 2 ^ 30 - 1 ∧
      t2.val.length + (rv.val.length + varint.lenOf rv.val.length) = bytes.val.length
    rw [hrl, hl2, hy]
    refine ⟨by omega, ?_⟩
    omega
  · intro v t h; cases h
  · exfalso
    rename_i r0 hP r1 p x1 r2 htf r3 residual x2 e hr2 h3
    have hb := (hP p.1 p.2 h3)
    obtain ⟨y, hy⟩ := htf.2 (by omega)
    rw [hy] at hr2
    cases hr2
  · intro _ v t h; cases h

/-- `VLByteVec::tls_serialized_len` of a payload of at most `2^30 - 1` bytes is the payload length plus
the minimal varint length prefix. -/
theorem quic_vec.VLByteVec.serialized_len_char (self : quic_vec.VLByteVec)
    (h : self.vec.val.length ≤ 2 ^ 30 - 1) :
    ⦃ ⌜ True ⌝ ⦄ quic_vec.VLByteVec.Insts.Tls_codecSize.tls_serialized_len self
    ⦃ ⇓ r => ⌜ r.val = self.vec.val.length + varint.lenOf self.vec.val.length ⌝ ⦄ := by
  mvcgen [quic_vec.VLByteVec.Insts.Tls_codecSize.tls_serialized_len, quic_vec.VLByteVec.as_slice,
    quic_vec.VLByteVec.impl.vec, quic_vec.tls_serialize_bytes_len_char]
  · intro hr; subst_vars; exact hr
  · intro hr; subst_vars; exact h


/-! ### Serializers with a varint length prefix (`Vec::extend`, `String`)

Only lengths are tracked: the contents of the varint prefix are not (see `write_bytes_spec`). -/

/-- `checked_alloc_len` of two small lengths is their sum. -/
theorem checked_alloc_len_small (a b : Std.Usize) (h : a.val + b.val < 2 ^ 31) :
    ⦃ ⌜ True ⌝ ⦄ checked_alloc_len a b
    ⦃ ⇓ r => ⌜ ∃ n : Std.Usize, r = .Ok n ∧ n.val = a.val + b.val ⌝ ⦄ := by
  have hm := Usize.hcast_Isize_MAX_val
  have hs := Usize_saturating_add_val a b (by omega)
  mvcgen [checked_alloc_len, checked_capacity, CoreModels.core.num.Usize.saturating_add_spec]
  · rename_i sat hsat hgt
    subst hsat
    exfalso; scalar_tac
  · rename_i sat hsat hle
    subst hsat
    exact ⟨_, rfl, hs⟩

/-- `Vec::<u8>::resize` sets the length. -/
theorem alloc.vec.Vec.resize_U8_len_spec (v : alloc.vec.Vec Std.U8) (n : Std.Usize) (x : Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.resize core.U8.Insts.CoreCloneClone v n x
    ⦃ ⇓ r => ⌜ (r : Slice Std.U8).val.length = n.val ⌝ ⦄ := by
  unfold alloc.vec.Vec.resize rust_primitives.sequence.seq_create
  simp only [mapM_clone_replicate_U8]
  mvcgen
  all_goals (simp_all +zetaDelta [Slice.new] <;> scalar_tac)

/-- `VLBytes::tls_serialize_bytes` never panics: a payload of at most `2^30 - 1` bytes gives the
varint length prefix followed by the payload (only the length is tracked), a longer one an error. -/
theorem quic_vec.VLBytes.serialize_char (self : quic_vec.VLBytes) :
    ⦃ ⌜ True ⌝ ⦄ quic_vec.VLBytes.Insts.Tls_codecSerializeBytes.tls_serialize_bytes self
    ⦃ ⇓ r => ⌜ (self.vec.val.length ≤ 2 ^ 30 - 1 → ∃ out : alloc.vec.Vec Std.U8, r = .Ok out ∧
                  out.val.length = self.vec.val.length + varint.lenOf self.vec.val.length) ∧
               (2 ^ 30 - 1 < self.vec.val.length → ∃ e, r = .Err e) ⌝ ⦄ := by
  mvcgen [quic_vec.VLBytes.Insts.Tls_codecSerializeBytes.tls_serialize_bytes,
    quic_vec.VLBytes.as_slice, quic_vec.VLBytes.impl.vec, alloc.vec.Vec.with_capacity,
    alloc.vec.Vec.resize_U8_len_spec, checked_alloc_len_small,
    alloc.vec.Vec.Insts.CoreOpsDerefDerefMutSlice.deref_mut, alloc.vec.Vec.as_mut_slice,
    rust_primitives.sequence.seq_to_slice_mut, varint.TlsVarInt.write_bytes_spec,
    alloc.vec.Vec.Insts.CoreIterTraitsCollectExtendSharedAT.extend_slice_spec]
  all_goals (try simp only [continue_eq_tryCF] at *)
  all_goals subst_vars
  all_goals (try simp only [Slice.len_val] at *)
  · -- `checked_alloc_len` gets small operands
    rename_i hr hv
    have := hr.2.1
    omega
  · -- room for the payload
    rename_i val r hr _ res hres back w hw _ out2 _ hv _
    have hc := varint.lenOf_char _ _ hr
    have hl := (hw.2 (by omega)).2
    show w.2.val.length + _ ≤ _
    have : Slice.length self.vec ≤ 2 ^ 30 - 1 := hv.2
    scalar_tac
  · -- the length check passes
    rename_i val r hr _ res hres back w hw _ out2 out3 i hw1 hout3 hne hv _ hi _
    have hc := varint.lenOf_char _ _ hr
    have hl := (hw.2 (by omega)).2
    have h3 : Slice.length out3 = w.2.val.length + Slice.length self.vec := by
      simp only [Slice.length, hout3, List.length_append]; rfl
    exfalso
    simp only [bne_iff_ne, ne_eq] at hne
    exact hne (by scalar_tac)
  · rename_i val r hr _ res hres back w hw _ out2 out3 i hw1 hout3 hne hv _ hi _
    have hc := varint.lenOf_char _ _ hr
    have hl := (hw.2 (by omega)).2
    have hv2 : self.vec.val.length ≤ 2 ^ 30 - 1 := hv.2
    refine ⟨fun _ => ⟨out3, rfl, ?_⟩, fun h => by omega⟩
    rw [hout3, List.length_append]
    show w.2.val.length + _ = _
    have : val.val = self.vec.val.length := hv.1
    scalar_tac
  · rename_i val r hr _ res hres back w hw _ out2 out3 hw1 hout3 hv _ hlt
    have hc := varint.lenOf_char _ _ hr
    have hl := (hw.2 (by omega)).2
    have h3 : Slice.length out3 = w.2.val.length + Slice.length self.vec := by
      simp only [Slice.length, hout3, List.length_append]; rfl
    exfalso; scalar_tac
  · -- `write_bytes` succeeds
    rename_i val r hr _ res hres back w hw resid hv _
    have hc := varint.lenOf_char _ _ hr
    obtain ⟨⟨l, hl, _⟩, _⟩ := hw.2 (by omega)
    intro hb
    rw [hl] at hb
    simp only [tryCF, reduceCtorEq] at hb
  · -- `checked_alloc_len` succeeds
    rename_i r resid hn _
    obtain ⟨n, rfl, _⟩ := hn
    intro hb
    simp only [tryCF, reduceCtorEq] at hb
  · -- `from_usize` fails: the payload is too long
    rename_i r resid hr
    apply try_break_vc
    intro e he
    subst he
    have hr' : 2 ^ 30 - 1 < self.vec.val.length := hr
    mvcgen
    intro _
    exact ⟨fun h => absurd h (by omega), fun _ => ⟨_, rfl⟩⟩

/-- `VLByteSlice::tls_serialize_bytes` never panics: a payload of at most `2^30 - 1` bytes gives the
varint length prefix followed by the payload (only the length is tracked), a longer one an error. -/
theorem quic_vec.VLByteSlice.serialize_char (self : quic_vec.VLByteSlice) :
    ⦃ ⌜ True ⌝ ⦄ quic_vec.VLByteSlice.Insts.Tls_codecSerializeBytes.tls_serialize_bytes self
    ⦃ ⇓ r => ⌜ (self.val.length ≤ 2 ^ 30 - 1 → ∃ out : alloc.vec.Vec Std.U8, r = .Ok out ∧
                  out.val.length = self.val.length + varint.lenOf self.val.length) ∧
               (2 ^ 30 - 1 < self.val.length → ∃ e, r = .Err e) ⌝ ⦄ := by
  mvcgen [quic_vec.VLByteSlice.Insts.Tls_codecSerializeBytes.tls_serialize_bytes,
    quic_vec.ContentLength.Insts.Tls_codecSize.tls_serialized_len,
    varint.TlsVarInt.Insts.Tls_codecSize.tls_serialized_len,
    quic_vec.ContentLength.Insts.Tls_codecSerializeBytes.tls_serialize_bytes,
    varint.TlsVarInt.serialize_len_char, alloc.vec.Vec.with_capacity, checked_alloc_len_small,
    alloc.vec.Vec.append, rust_primitives.sequence.seq_concat,
    alloc.vec.Vec.Insts.CoreIterTraitsCollectExtendSharedAT.extend_slice_spec]
  all_goals (try simp only [continue_eq_tryCF] at *)
  all_goals subst_vars
  all_goals (try simp only [Slice.len_val] at *)
  · rename_i hr hv
    have := hr.2.1
    omega
  · -- room for the payload after the prefix
    rename_i val r hr _ v1 comb hcomb hv1 hv _
    obtain ⟨v, hv', hl⟩ := hv1
    cases hv'
    have hv2 : self.val.length ≤ 2 ^ 30 - 1 := hv.2
    have hlo : varint.lenOf val.val ≤ 8 := by unfold varint.lenOf; split_ifs <;> omega
    simp only [comb, List.length_append, hl]
    simp only [Slice.new, List.length_nil]
    scalar_tac
  · rename_i val r hr _ v1 out comb hcomb hout hv1 hv _
    obtain ⟨v, hv', hl⟩ := hv1
    cases hv'
    have hv2 : self.val.length ≤ 2 ^ 30 - 1 := hv.2
    have hvl : val.val = self.val.length := hv.1
    refine ⟨fun _ => ⟨out, rfl, ?_⟩, fun h => by omega⟩
    simp only [hout, comb, List.length_append, hl, hvl]
    simp only [Slice.new, List.length_nil]
    omega
  · rename_i val r hr _ v1 comb hcomb hv1 hv _
    obtain ⟨v, hv', hl⟩ := hv1
    cases hv'
    have hv2 : self.val.length ≤ 2 ^ 30 - 1 := hv.2
    have hlo : varint.lenOf val.val ≤ 8 := by unfold varint.lenOf; split_ifs <;> omega
    exfalso; apply hcomb
    simp only [comb, List.length_append, hl]
    simp only [Slice.new, List.length_nil]
    scalar_tac
  · -- the prefix serializes
    rename_i val r hr _ x hx resid hv _
    obtain ⟨v, rfl, _⟩ := hx
    intro hb
    simp only [tryCF, reduceCtorEq] at hb
  · -- `checked_alloc_len` succeeds
    rename_i r resid hn _
    obtain ⟨n, rfl, _⟩ := hn
    intro hb
    simp only [tryCF, reduceCtorEq] at hb
  · -- `from_usize` fails: the payload is too long
    rename_i r resid hr
    apply try_break_vc
    intro e he
    subst he
    have hr' : 2 ^ 30 - 1 < self.val.length := hr
    mvcgen
    intro _
    exact ⟨fun h => absurd h (by omega), fun _ => ⟨_, rfl⟩⟩

/-- The fold of `<&[u8]>::tls_serialized_len` counts the bytes (each `u8` has size 1). -/
theorem Shared0Slice.size_fold_U8_spec (it : core.slice.iter.Iter Std.U8) (acc : Std.Usize)
    (h : acc.val + (it : Slice Std.U8).val.length ≤ Usize.max) :
    ⦃ ⌜ True ⌝ ⦄
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold
      (quic_vec.SizeShared0Slice.tls_serialized_len.closure.Insts.CoreOpsFunctionFnMutPairUsizeSharedTUsize
        U8.Insts.Tls_codecSize) it acc ()
    ⦃ ⇓ r => ⌜ r.val = acc.val + (it : Slice Std.U8).val.length ⌝ ⦄ := by
  simp only [core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold,
    core.iter.traits.iterator.Iterator.fold.default, core.iter.traits.iterator.iter_fold,
    core.iter.traits.iterator.iter_fold_loop]
  apply Aeneas.Std.WP.spec_to_mvcgen
  apply Aeneas.Std.loop.spec_decr_nat
    (fun p : core.slice.iter.Iter Std.U8 × quic_vec.SizeShared0Slice.tls_serialized_len.closure Std.U8
        × Std.Usize => (p.1 : Slice Std.U8).val.length)
    (fun p => p.2.2.val + (p.1 : Slice Std.U8).val.length = acc.val + (it : Slice Std.U8).val.length)
  · rintro ⟨it', c, a⟩ hinv
    simp only [core.iter.traits.iterator.iter_fold_loop.body,
      core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
      rust_primitives.sequence.seq_len, rust_primitives.sequence.seq_remove,
      quic_vec.SizeShared0Slice.tls_serialized_len.closure.Insts.CoreOpsFunctionFnMutPairUsizeSharedTUsize.call_mut,
      U8.Insts.Tls_codecSize.tls_serialized_len, len_add] at hinv ⊢
    by_cases hz : Slice.len it' = 0#usize
    · have : (it' : Slice Std.U8).val = [] := by
        rw [← List.length_eq_zero_iff]; scalar_tac
      simp_all
    · have hpos : 0 < (it' : Slice Std.U8).val.length := by scalar_tac
      have hadd := UScalar.add_equiv a 1#usize
      split at hadd
      · rename_i z hz'
        obtain ⟨_, hzv, _⟩ := hadd
        simp [hz, hpos, hz']
        scalar_tac
      · exfalso
        obtain ⟨_, hnb⟩ := hadd
        apply hnb
        simp only [UScalar.inBounds]
        scalar_tac
      · cases hadd
  · rfl

/-- `Result::map` with the length closure of `<&[T]>::tls_serialized_len`: an `Ok` content length
is mapped to `Ok` of its varint length, an `Err` is passed through. -/
theorem Shared0Slice.size_closure_map_spec {T : Type} (SizeInst : Size T)
    (x : core.result.Result quic_vec.ContentLength Error) :
    ⦃ ⌜ True ⌝ ⦄
    core.result.Result.map
      (quic_vec.SizeShared0Slice.tls_serialized_len.closure_1.Insts.CoreOpsFunctionFnOnceTupleContentLengthUsize
        SizeInst) x ()
    ⦃ ⇓ r => ⌜ (∀ t, x = .Ok t → ∃ u, r = .Ok u ∧ u.val = varint.lenOf t.val) ∧
               (∀ e, x = .Err e → r = .Err e) ⌝ ⦄ := by
  apply CoreModels.core.result.Result.map_spec
  · intro t ht
    mvcgen [quic_vec.SizeShared0Slice.tls_serialized_len.closure_1.Insts.CoreOpsFunctionFnOnceTupleContentLengthUsize.call_once]
    intro h1 h2 h3 h4 h5 h6
    subst ht
    refine ⟨fun t' h => ?_, fun e h => ?_⟩
    · obtain rfl := core.result.Result.Ok.inj h
      exact ⟨_, rfl, (varint.lenOf_char _ _ ⟨h1, h2, h3, h4, h5, h6⟩).1⟩
    · cases h
  · intro e he; subst he; simp [PostCond.ok]

/-- `<&[u8]>::tls_serialized_len` never panics: the length plus its varint prefix length (no prefix
counted above the `2^30 - 1` bound, where `ContentLength::from_usize` fails). -/
theorem Shared0Slice.size_U8_char (s : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ Shared0Slice.Insts.Tls_codecSize.tls_serialized_len U8.Insts.Tls_codecSize s
    ⦃ ⇓ r => ⌜ r.val = s.val.length +
        (if s.val.length ≤ 2 ^ 30 - 1 then varint.lenOf s.val.length else 0) ⌝ ⦄ := by
  have hs := s.property
  mvcgen [Shared0Slice.Insts.Tls_codecSize.tls_serialized_len, Shared0Slice.size_fold_U8_spec,
    Shared0Slice.size_closure_map_spec, len_add]
  · subst_vars; scalar_tac
  · rename_i it hit n hn rc hrc rm hrm l hl sum hsum
    subst hit
    cases rc with
    | Ok c =>
      obtain ⟨u, rfl, hul⟩ := hrm.1 c rfl
      simp only at hl hrc
      subst hl
      rw [if_pos (by scalar_tac)]
      have hc : c.val = it.val.length := by scalar_tac
      rw [hsum, hul, hc]
      scalar_tac
    | Err e =>
      obtain rfl := hrm.2 e rfl
      simp only at hl hrc
      subst hl
      rw [if_neg (by scalar_tac)]
      scalar_tac
  · rename_i it hit n hn rc hrc rm hrm l hl hov
    subst hit
    exfalso
    cases rc with
    | Ok c =>
      obtain ⟨u, rfl, hul⟩ := hrm.1 c rfl
      simp only at hl hrc
      subst hl
      have : varint.lenOf c.val ≤ 8 := by unfold varint.lenOf; split_ifs <;> omega
      scalar_tac
    | Err e =>
      obtain rfl := hrm.2 e rfl
      simp only at hl hrc
      subst hl
      scalar_tac

/-- `String::tls_deserialize_bytes` never panics; on success the bytes of the string are the payload
that `VLByteVec::tls_deserialize_bytes` reads from the same input, with the same remainder. -/
theorem alloc.string.String.deserialize_char (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ alloc.string.String.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ t rem, r = .Ok (t, rem) → ∃ raw : quic_vec.VLByteVec,
        quic_vec.VLByteVec.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes bytes = ok (.Ok (raw, rem)) ∧
        alloc.string.String.utf8U8 t = raw.vec.val ⌝ ⦄ := by
  obtain ⟨r0, hr0, hP⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp (quic_vec.VLByteVec.deserialize_char bytes)
  unfold alloc.string.String.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes
  rw [hr0]
  mvcgen [core.result.Result.map_err_spec, alloc.vec.VecU8.Insts.CoreConvertFromVLByteVec.from,
    string.DeserializeBytesString.tls_deserialize_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleFromUtf8ErrorError.call_once]
  try_vcs
  · rename_i p _ hp r1 hr1 t1 ht1 _ v _ hv
    simp only [continue_eq_tryCF, core.result.Result.Ok.injEq] at hp hv
    subst hv ht1
    intro t rem h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (core.result.Result.Ok.inj h)
    obtain ⟨t', ht', hu⟩ | ⟨h1, _⟩ := hr1
    · cases ht'
      exact ⟨p.1, by rw [hp], hu⟩
    · cases h1
  · simp only [PostCond.ok]
    mvcgen
    try_vcs
    intro _ t rem h
    cases h
  · intro _ t rem h
    cases h

/-- `usize::try_from(u8)` through the blanket `TryFrom` impl for `Into` (`Error = Infallible`):
`Ok` of the widening cast. -/
@[spec]
theorem core.convert.TryFromTUInfallible.Blanket.try_from_Usize_U8_spec (x : Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
    core.convert.TryFromTUInfallible.Blanket.try_from
      (core.convert.Into.Blanket core.Usize.Insts.CoreConvertFromU8) x
    ⦃ ⇓ r => ⌜ r = .Ok (UScalar.cast .Usize x) ⌝ ⦄ := by
  unfold core.convert.TryFromTUInfallible.Blanket.try_from core.convert.Into.Blanket
  mvcgen [core.convert.Into.Blanket.into, CoreModels.core.Usize.Insts.CoreConvertFromU8.from_spec]
  subst_vars; rfl

/-- `Result::unwrap` of a value that is `Ok` (the `Err` case panics, so it is excluded by
hypothesis; used for `Result<_, Infallible>`). -/
@[spec]
theorem core.result.Result.unwrap_ok_spec {T E : Type} (fmtDebugInst : core.fmt.Debug E)
    (x : core.result.Result T E) (h : ∃ t, x = .Ok t) :
    ⦃ ⌜ True ⌝ ⦄ core.result.Result.unwrap fmtDebugInst x ⦃ ⇓ r => ⌜ x = .Ok r ⌝ ⦄ := by
  obtain ⟨t, rfl⟩ := h
  unfold core.result.Result.unwrap
  mvcgen

/-- `usize::checked_add`: `Some (x + y)` exactly when the sum does not overflow. -/
@[spec]
theorem core.num.Usize.checked_add_spec (x y : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ core.num.Usize.checked_add x y
    ⦃ ⇓ r => ⌜ (x.val + y.val ≤ Std.Usize.max → ∃ z : Std.Usize, r = some z ∧ z.val = x.val + y.val) ∧
               (Std.Usize.max < x.val + y.val → r = none) ⌝ ⦄ := by
  mvcgen [core.num.Usize.checked_add, core.num.Usize.overflowing_add]
  · rename_i hov
    have h := UScalar.overflowing_add_eq x y
    simp only [hov] at h
    by_cases hc : x.val + y.val > UScalar.max .Usize
    · simp only [if_pos hc] at h
      refine ⟨fun hle => ?_, fun _ => trivial⟩
      scalar_tac
    · simp only [if_neg hc] at h
      exact absurd h.2 (by simp)
  · rename_i hov
    have h := UScalar.overflowing_add_eq x y
    simp only [Bool.not_eq_true] at hov
    simp only [hov] at h
    by_cases hc : x.val + y.val > UScalar.max .Usize
    · simp only [if_pos hc] at h
      exact absurd h.2 (by simp)
    · simp only [if_neg hc] at h
      refine ⟨fun _ => ⟨_, rfl, by scalar_tac⟩, fun hlt => ?_⟩
      scalar_tac

/-- `s.get(start..end)`: if it returns `Some t`, the range is in bounds and `t` has `end - start`
elements. -/
@[spec]
theorem core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_some_spec
    {T : Type} (r : core.ops.range.Range Std.Usize) (s : Slice T) :
    ⦃ ⌜ True ⌝ ⦄ core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get r s
    ⦃ ⇓ o => ⌜ ∀ t, o = some t → r.start.val ≤ r.end.val ∧ r.end.val ≤ s.val.length ∧
        t.val.length = r.end.val - r.start.val ⌝ ⦄ := by
  unfold core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get
    rust_primitives.slice.slice_length rust_primitives.slice.slice_slice Slice.subslice
  mvcgen
  · rename_i h1 h2 h3
    have hl : (s.len).val = s.val.length := by simp
    intro t ht
    have ht' := Option.some.inj ht
    subst ht'
    refine ⟨h3.1, h3.2, ?_⟩
    have h4 : r.end.val ≤ s.val.length := h3.2
    have h5 : r.start.val ≤ r.end.val := h3.1
    simp [List.slice]
    omega
  · rename_i h1 h2 h3
    exfalso; apply h3
    have hl : (s.len).val = s.val.length := by simp
    exact ⟨by scalar_tac, by scalar_tac⟩
  · intro t ht; cases ht
  · intro t ht; cases ht

/-- `TlsByteVecU8::deserialize_bytes_bytes` never panics; on success the remainder plus the
length prefix plus the payload is the input. -/
theorem tls_vec.TlsByteVecU8.deserialize_char (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU8.deserialize_bytes_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : tls_vec.TlsByteVecU8) (t : Slice Std.U8), r = .Ok (v, t) →
        t.val.length + 1 + v.vec.val.length = bytes.val.length ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU8.deserialize_bytes_bytes, U8_deserialize_char,
    core.option.Option.ok_or_spec]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  · exact ⟨_, ‹_›⟩
  · rename_i r0 hP r1 p x1 r2 htf r3 hr3 o hca r4 hr4 cf1 val x2 o1 hget1 r5 hr5 cf2 val1 x3
      vec hvec o2 hget2 r6 hr6 cf3 val2 x4 e0 e1 e2 e3
    intro v t h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (core.result.Result.Ok.inj h)
    have hl : 1 ≤ bytes.val.length := by
      by_contra hn
      rw [hP.2 (by omega)] at e0
      cases e0
    obtain ⟨a, tt, _, htt, hr⟩ := hP.1 hl
    rw [hr] at e0
    have hp := core.result.Result.Ok.inj e0
    have hpt : p.2 = tt := by rw [← hp]
    have hp2 : p.2.val.length = bytes.val.length - 1 := by rw [hpt, htt]; simp
    have h1 := hget1 val1 (ok_or_eq_ok hr5 e2)
    have h2 : val.val = r3.val + 1 := by
      by_cases hov : r3.val + (1#usize).val ≤ Usize.max
      · obtain ⟨z, hz1, hz2⟩ := hca.1 hov
        rw [hz1] at hr4
        have := core.result.Result.Ok.inj (hr4.symm.trans e1)
        subst this
        simpa using hz2
      · have := hca.2 (by omega)
        rw [this] at hr4
        rw [hr4] at e1
        cases e1
    have ho2 := ok_or_eq_ok hr6 e3
    have hle : r3.val ≤ p.2.val.length := by
      by_contra hn
      rw [hget2.2 (by omega)] at ho2
      cases ho2
    obtain ⟨t2, ht2, ht2'⟩ := hget2.1 hle
    rw [ht2] at ho2
    have hv2 := Option.some.inj ho2
    subst hv2
    have h3 : t2.val.length = p.2.val.length - r3.val := by rw [ht2']; simp
    subst hvec
    show t2.val.length + 1 + vec.val.length = bytes.val.length
    have hone : (1#usize).val = 1 := rfl
    omega
  · intro _ v t h; cases h
  · intro _ v t h; cases h
  · intro _ v t h; cases h
  · intro _ v t h; cases h

/-- `usize::from(u16)`. -/
@[spec]
theorem core.Usize.Insts.CoreConvertFromU16.from_spec (x : Std.U16) :
    ⦃ ⌜ True ⌝ ⦄ core.Usize.Insts.CoreConvertFromU16.from x
    ⦃ ⇓ r => ⌜ r = UScalar.cast .Usize x ⌝ ⦄ := by
  unfold core.Usize.Insts.CoreConvertFromU16.from; mvcgen

/-- `usize::try_from(u16)` through the blanket `TryFrom` impl for `Into` (`Error = Infallible`). -/
@[spec]
theorem core.convert.TryFromTUInfallible.Blanket.try_from_Usize_U16_spec (x : Std.U16) :
    ⦃ ⌜ True ⌝ ⦄
    core.convert.TryFromTUInfallible.Blanket.try_from
      (core.convert.Into.Blanket core.Usize.Insts.CoreConvertFromU16) x
    ⦃ ⇓ r => ⌜ r = .Ok (UScalar.cast .Usize x) ⌝ ⦄ := by
  unfold core.convert.TryFromTUInfallible.Blanket.try_from core.convert.Into.Blanket
  mvcgen [core.convert.Into.Blanket.into, core.Usize.Insts.CoreConvertFromU16.from_spec]
  subst_vars; rfl

/-- `usize::try_from(u32)`: always `Ok` of the widening cast (`usize` is at least 32 bits). -/
@[spec]
theorem core.Usize.Insts.CoreConvertTryFromU32TryFromIntError.try_from_spec (x : Std.U32) :
    ⦃ ⌜ True ⌝ ⦄ core.Usize.Insts.CoreConvertTryFromU32TryFromIntError.try_from x
    ⦃ ⇓ r => ⌜ r = .Ok (UScalar.cast .Usize x) ⌝ ⦄ := by
  unfold core.Usize.Insts.CoreConvertTryFromU32TryFromIntError.try_from; mvcgen
  subst_vars; rfl

/-- `TlsByteVecU16::deserialize_bytes_bytes` never panics; on success the remainder plus the
length prefix plus the payload is the input. -/
theorem tls_vec.TlsByteVecU16.deserialize_char (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU16.deserialize_bytes_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : tls_vec.TlsByteVecU16) (t : Slice Std.U8), r = .Ok (v, t) →
        t.val.length + 2 + v.vec.val.length = bytes.val.length ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU16.deserialize_bytes_bytes, U16_deserialize_char,
    core.option.Option.ok_or_spec]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  · exact ⟨_, ‹_›⟩
  · rename_i r0 hP r1 p x1 r2 htf r3 hr3 o hca r4 hr4 cf1 val x2 o1 hget1 r5 hr5 cf2 val1 x3
      vec hvec o2 hget2 r6 hr6 cf3 val2 x4 e0 e1 e2 e3
    intro v t h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (core.result.Result.Ok.inj h)
    have hl : 2 ≤ bytes.val.length := by
      by_contra hn
      rw [hP.2 (by omega)] at e0
      cases e0
    obtain ⟨a, tt, _, htt, hr⟩ := hP.1 hl
    rw [hr] at e0
    have hp := core.result.Result.Ok.inj e0
    have hpt : p.2 = tt := by rw [← hp]
    have hp2 : p.2.val.length = bytes.val.length - 2 := by rw [hpt, htt]; simp
    have h1 := hget1 val1 (ok_or_eq_ok hr5 e2)
    have h2 : val.val = r3.val + 2 := by
      by_cases hov : r3.val + (2#usize).val ≤ Usize.max
      · obtain ⟨z, hz1, hz2⟩ := hca.1 hov
        rw [hz1] at hr4
        have := core.result.Result.Ok.inj (hr4.symm.trans e1)
        subst this
        simpa using hz2
      · have := hca.2 (by omega)
        rw [this] at hr4
        rw [hr4] at e1
        cases e1
    have ho2 := ok_or_eq_ok hr6 e3
    have hle : r3.val ≤ p.2.val.length := by
      by_contra hn
      rw [hget2.2 (by omega)] at ho2
      cases ho2
    obtain ⟨t2, ht2, ht2'⟩ := hget2.1 hle
    rw [ht2] at ho2
    have hv2 := Option.some.inj ho2
    subst hv2
    have h3 : t2.val.length = p.2.val.length - r3.val := by rw [ht2']; simp
    subst hvec
    show t2.val.length + 2 + vec.val.length = bytes.val.length
    have hone : (2#usize).val = 2 := rfl
    omega
  · intro _ v t h; cases h
  · intro _ v t h; cases h
  · intro _ v t h; cases h
  · intro _ v t h; cases h

/-- `TlsByteVecU32::deserialize_bytes_bytes` never panics; on success the remainder plus the
length prefix plus the payload is the input. -/
theorem tls_vec.TlsByteVecU32.deserialize_char (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU32.deserialize_bytes_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : tls_vec.TlsByteVecU32) (t : Slice Std.U8), r = .Ok (v, t) →
        t.val.length + 4 + v.vec.val.length = bytes.val.length ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU32.deserialize_bytes_bytes, U32_deserialize_char,
    core.option.Option.ok_or_spec]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  · exact ⟨_, ‹_›⟩
  · rename_i r0 hP r1 p x1 r2 htf r3 hr3 o hca r4 hr4 cf1 val x2 o1 hget1 r5 hr5 cf2 val1 x3
      vec hvec o2 hget2 r6 hr6 cf3 val2 x4 e0 e1 e2 e3
    intro v t h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (core.result.Result.Ok.inj h)
    have hl : 4 ≤ bytes.val.length := by
      by_contra hn
      rw [hP.2 (by omega)] at e0
      cases e0
    obtain ⟨a, tt, _, htt, hr⟩ := hP.1 hl
    rw [hr] at e0
    have hp := core.result.Result.Ok.inj e0
    have hpt : p.2 = tt := by rw [← hp]
    have hp2 : p.2.val.length = bytes.val.length - 4 := by rw [hpt, htt]; simp
    have h1 := hget1 val1 (ok_or_eq_ok hr5 e2)
    have h2 : val.val = r3.val + 4 := by
      by_cases hov : r3.val + (4#usize).val ≤ Usize.max
      · obtain ⟨z, hz1, hz2⟩ := hca.1 hov
        rw [hz1] at hr4
        have := core.result.Result.Ok.inj (hr4.symm.trans e1)
        subst this
        simpa using hz2
      · have := hca.2 (by omega)
        rw [this] at hr4
        rw [hr4] at e1
        cases e1
    have ho2 := ok_or_eq_ok hr6 e3
    have hle : r3.val ≤ p.2.val.length := by
      by_contra hn
      rw [hget2.2 (by omega)] at ho2
      cases ho2
    obtain ⟨t2, ht2, ht2'⟩ := hget2.1 hle
    rw [ht2] at ho2
    have hv2 := Option.some.inj ho2
    subst hv2
    have h3 : t2.val.length = p.2.val.length - r3.val := by rw [ht2']; simp
    subst hvec
    show t2.val.length + 4 + vec.val.length = bytes.val.length
    have hone : (4#usize).val = 4 := rfl
    omega
  · intro _ v t h; cases h
  · intro _ v t h; cases h
  · intro _ v t h; cases h
  · intro _ v t h; cases h

/-- `TlsByteVecU8::tls_serialized_len` is the payload length plus the one-byte length prefix (when
that does not overflow `usize`). -/
theorem tls_vec.TlsByteVecU8.serialized_len_char (self : tls_vec.TlsByteVecU8)
    (h : self.vec.val.length + 1 ≤ Std.Usize.max) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU8.Insts.Tls_codecSize.tls_serialized_len self
    ⦃ ⇓ r => ⌜ r.val = self.vec.val.length + 1 ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU8.Insts.Tls_codecSize.tls_serialized_len,
    tls_vec.TlsByteVecU8.tls_serialized_byte_length, tls_vec.TlsByteVecU8.as_slice,
    CoreModels.core.slice.Slice.len_spec]
  · rename_i s hs n hn r hr
    subst hs; subst hn
    simp only [Slice.len] at hr
    scalar_tac
  · rename_i s hs n hn hov
    subst hs; subst hn
    simp only [Slice.len] at hov
    scalar_tac

/-- `TlsByteVecU16::tls_serialized_len` is the payload length plus the 2-byte length prefix (when
that does not overflow `usize`). -/
theorem tls_vec.TlsByteVecU16.serialized_len_char (self : tls_vec.TlsByteVecU16)
    (h : self.vec.val.length + 2 ≤ Std.Usize.max) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU16.Insts.Tls_codecSize.tls_serialized_len self
    ⦃ ⇓ r => ⌜ r.val = self.vec.val.length + 2 ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU16.Insts.Tls_codecSize.tls_serialized_len,
    tls_vec.TlsByteVecU16.tls_serialized_byte_length, tls_vec.TlsByteVecU16.as_slice,
    CoreModels.core.slice.Slice.len_spec]
  · rename_i s hs n hn r hr
    subst hs; subst hn
    simp only [Slice.len] at hr
    scalar_tac
  · rename_i s hs n hn hov
    subst hs; subst hn
    simp only [Slice.len] at hov
    scalar_tac

/-- `TlsByteVecU24::tls_serialized_len` is the payload length plus the 3-byte length prefix (when
that does not overflow `usize`). -/
theorem tls_vec.TlsByteVecU24.serialized_len_char (self : tls_vec.TlsByteVecU24)
    (h : self.vec.val.length + 3 ≤ Std.Usize.max) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU24.Insts.Tls_codecSize.tls_serialized_len self
    ⦃ ⇓ r => ⌜ r.val = self.vec.val.length + 3 ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU24.Insts.Tls_codecSize.tls_serialized_len,
    tls_vec.TlsByteVecU24.tls_serialized_byte_length, tls_vec.TlsByteVecU24.as_slice,
    CoreModels.core.slice.Slice.len_spec]
  · rename_i s hs n hn r hr
    subst hs; subst hn
    simp only [Slice.len] at hr
    scalar_tac
  · rename_i s hs n hn hov
    subst hs; subst hn
    simp only [Slice.len] at hov
    scalar_tac

/-- `TlsByteVecU32::tls_serialized_len` is the payload length plus the 4-byte length prefix (when
that does not overflow `usize`). -/
theorem tls_vec.TlsByteVecU32.serialized_len_char (self : tls_vec.TlsByteVecU32)
    (h : self.vec.val.length + 4 ≤ Std.Usize.max) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU32.Insts.Tls_codecSize.tls_serialized_len self
    ⦃ ⇓ r => ⌜ r.val = self.vec.val.length + 4 ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU32.Insts.Tls_codecSize.tls_serialized_len,
    tls_vec.TlsByteVecU32.tls_serialized_byte_length, tls_vec.TlsByteVecU32.as_slice,
    CoreModels.core.slice.Slice.len_spec]
  · rename_i s hs n hn r hr
    subst hs; subst hn
    simp only [Slice.len] at hr
    scalar_tac
  · rename_i s hs n hn hov
    subst hs; subst hn
    simp only [Slice.len] at hov
    scalar_tac

/-- `usize::from(U24)` has no total spec (it panics when `usize` is 32 bits wide), but as a partial
triple it says nothing: only used to feed the `⇓?` spec of the blanket `try_from` below. -/
theorem Usize.Insts.CoreConvertFromU24.from_partial (v : U24) :
    ⦃ ⌜ True ⌝ ⦄ Usize.Insts.CoreConvertFromU24.from v ⦃ ⇓? _ => ⌜ True ⌝ ⦄ :=
  partial_triple_of_ok (fun _ _ => trivial)

/-- `usize::try_from(U24)` through the blanket `TryFrom` impl for `Into`: when it returns, it is
`Ok` (partial triple, as `Usize.Insts.CoreConvertFromU24.from` may panic). -/
theorem core.convert.TryFromTUInfallible.Blanket.try_from_Usize_U24_partial (x : U24) :
    ⦃ ⌜ True ⌝ ⦄
    core.convert.TryFromTUInfallible.Blanket.try_from
      (core.convert.Into.Blanket Usize.Insts.CoreConvertFromU24) x
    ⦃ ⇓? r => ⌜ ∃ y, r = .Ok y ⌝ ⦄ := by
  unfold core.convert.TryFromTUInfallible.Blanket.try_from core.convert.Into.Blanket
  mvcgen [core.convert.Into.Blanket.into, Usize.Insts.CoreConvertFromU24.from_partial]
  exact ⟨_, rfl⟩

/-- `TlsByteVecU24::deserialize_bytes_bytes` returns (it may panic on 32-bit `usize`, so this is a partial triple); on success the remainder plus the
length prefix plus the payload is the input. -/
theorem tls_vec.TlsByteVecU24.deserialize_char_partial (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU24.deserialize_bytes_bytes bytes
    ⦃ ⇓? r => ⌜ ∀ (v : tls_vec.TlsByteVecU24) (t : Slice Std.U8), r = .Ok (v, t) →
        t.val.length + 3 + v.vec.val.length = bytes.val.length ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU24.deserialize_bytes_bytes, U24_deserialize_char,
    core.convert.TryFromTUInfallible.Blanket.try_from_Usize_U24_partial,
    core.option.Option.ok_or_spec]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  · rename_i r0 hP r1 p x1 r2 htf r3 hr3 o hca r4 hr4 cf1 val x2 o1 hget1 r5 hr5 cf2 val1 x3
      vec hvec o2 hget2 r6 hr6 cf3 val2 x4 e0 e1 e2 e3
    intro v t h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (core.result.Result.Ok.inj h)
    have hl : 3 ≤ bytes.val.length := by
      by_contra hn
      rw [hP.2 (by omega)] at e0
      cases e0
    obtain ⟨a, tt, _, htt, hr⟩ := hP.1 hl
    rw [hr] at e0
    have hp := core.result.Result.Ok.inj e0
    have hpt : p.2 = tt := by rw [← hp]
    have hp2 : p.2.val.length = bytes.val.length - 3 := by rw [hpt, htt]; simp
    have h1 := hget1 val1 (ok_or_eq_ok hr5 e2)
    have h2 : val.val = r3.val + 3 := by
      by_cases hov : r3.val + (3#usize).val ≤ Usize.max
      · obtain ⟨z, hz1, hz2⟩ := hca.1 hov
        rw [hz1] at hr4
        have := core.result.Result.Ok.inj (hr4.symm.trans e1)
        subst this
        simpa using hz2
      · have := hca.2 (by omega)
        rw [this] at hr4
        rw [hr4] at e1
        cases e1
    have ho2 := ok_or_eq_ok hr6 e3
    have hle : r3.val ≤ p.2.val.length := by
      by_contra hn
      rw [hget2.2 (by omega)] at ho2
      cases ho2
    obtain ⟨t2, ht2, ht2'⟩ := hget2.1 hle
    rw [ht2] at ho2
    have hv2 := Option.some.inj ho2
    subst hv2
    have h3 : t2.val.length = p.2.val.length - r3.val := by rw [ht2']; simp
    subst hvec
    show t2.val.length + 3 + vec.val.length = bytes.val.length
    have hone : (3#usize).val = 3 := rfl
    omega
  · intro _ v t h; cases h
  · intro _ v t h; cases h
  · intro _ v t h; cases h
  · intro _ v t h; cases h

/-! ### Hand-translated opaque bodies (`Assumptions/FunsExternal.lean`)

`Assumptions/` is compiled before `Extraction/Funs.lean`, so the hand-written bodies of
`get_content_lengths`, `<&[T]>::tls_serialize_bytes` and `<Box<T>>::tls_deserialize_bytes`
call verbatim copies (`tls_codec.Copied.*`) of the crate functions they need. Each copy is
equal to its original; rewrite with these to reuse the originals' specs. -/

namespace Copied
theorem checked_len_add_eq : checked_len_add = _root_.tls_codec.checked_len_add := rfl
theorem checked_alloc_len_eq : checked_alloc_len = _root_.tls_codec.checked_alloc_len := rfl
theorem U24.MAX_eq : U24.MAX = _root_.tls_codec.U24.MAX := by with_unfolding_all rfl
theorem Usize.Insts.CoreConvertFromU24_eq :
    Usize.Insts.CoreConvertFromU24 = _root_.tls_codec.Usize.Insts.CoreConvertFromU24 := by
  with_unfolding_all rfl
theorem U8.Insts.Tls_codecSize.tls_serialized_len_eq :
    U8.Insts.Tls_codecSize.tls_serialized_len =
      _root_.tls_codec.U8.Insts.Tls_codecSize.tls_serialized_len := rfl
theorem quic_vec.ContentLength.from_usize_eq :
    quic_vec.ContentLength.from_usize = _root_.tls_codec.quic_vec.ContentLength.from_usize := by
  with_unfolding_all rfl
theorem varint.TlsVarInt.bytes_len_eq :
    varint.TlsVarInt.bytes_len = _root_.tls_codec.varint.TlsVarInt.bytes_len := rfl
theorem varint.TlsVarInt.write_bytes_eq :
    varint.TlsVarInt.write_bytes = _root_.tls_codec.varint.TlsVarInt.write_bytes := rfl
end Copied

/-! ### Specs of the hand-translated `get_content_lengths` -/

/-- `Vec` deref and `slice::iter` are the identity (re-packed, so the result is type-correct at
instance transparency and `bind_tc_ok` can fire after `erw`). -/
theorem deref_vec_ok {T : Type} (v : alloc.vec.Vec T) :
    alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref v = RustM.ok (⟨v.val, v.property⟩ : Slice T) := rfl
theorem slice_iter_ok {T : Type} (s : Slice T) :
    core.slice.Slice.iter s = RustM.ok (⟨s.val, s.property⟩ : core.slice.iter.Iter T) := rfl

/-- A `loop` that walks a slice iterator and adds `c` to an accumulator per element (the
`try_fold` of the length sums in the hand-translated bodies). `hbody`: one step. -/
theorem loop_len_sum_spec {T : Type} (c : Std.Usize) (it : core.slice.iter.Iter T) (acc : Std.Usize)
    (body : core.slice.iter.Iter T × Std.Usize →
      RustM (ControlFlow (core.slice.iter.Iter T × Std.Usize) (core.result.Result Std.Usize Error)))
    (h : acc.val + c.val * (it : Slice T).val.length ≤ Usize.max)
    (hbody : ∀ (it' : core.slice.iter.Iter T) (a : Std.Usize),
      a.val + c.val * (it' : Slice T).val.length ≤ Usize.max →
      ⦃ ⌜ True ⌝ ⦄ body (it', a)
      ⦃ ⇓ r => ⌜ match r with
        | .done y => y = .Ok a ∧ (it' : Slice T).val.length = 0
        | .cont p => p.2.val = a.val + c.val ∧ (p.1 : Slice T).val.length + 1 = (it' : Slice T).val.length ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄ loop body (it, acc)
    ⦃ ⇓ r => ⌜ ∃ v : Std.Usize, r = .Ok v ∧ v.val = acc.val + c.val * (it : Slice T).val.length ⌝ ⦄ := by
  apply Aeneas.Std.WP.spec_to_mvcgen
  apply Aeneas.Std.loop.spec_decr_nat
    (fun p : core.slice.iter.Iter T × Std.Usize => (p.1 : Slice T).val.length)
    (fun p => p.2.val + c.val * (p.1 : Slice T).val.length = acc.val + c.val * (it : Slice T).val.length)
  · rintro ⟨it', a⟩ hinv
    have hb := Aeneas.Std.WP.exists_imp_spec
      (Aeneas.Std.WP.triple_iff_exists_ok.mp (hbody it' a (by simp only at hinv; omega)))
    apply Aeneas.Std.WP.spec_mono hb
    intro r hr
    simp only at hinv
    cases r with
    | done y =>
      obtain ⟨rfl, hl⟩ := hr
      exact ⟨a, rfl, by rw [hl] at hinv; omega⟩
    | cont p =>
      obtain ⟨ha, hl⟩ := hr
      refine ⟨?_, by simp only; omega⟩
      rw [← hl, Nat.mul_succ] at hinv
      omega
  · simp

/-- Sequencing through a total step: if `x` returns with `P`, any post of `x >>= f` follows from
the posts of `f` on the `P` values (for `⇓` and `⇓?` alike). -/
theorem triple_bind_of_total {α β : Type} {x : RustM α} {f : α → RustM β} {P : α → Prop}
    {Q : Std.Do.PostCond β (Std.Do.PostShape.except (ULift Std.Error) (Std.Do.PostShape.except PUnit.{1} Std.Do.PostShape.pure))}
    (hx : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) (hf : ∀ r, P r → ⦃ ⌜ True ⌝ ⦄ f r ⦃ Q ⦄) :
    ⦃ ⌜ True ⌝ ⦄ (x >>= f) ⦃ Q ⦄ := by
  obtain ⟨a, rfl, ha⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp hx
  simpa using hf a ha

/-- `get_content_lengths` of a `TlsByteVecU8` of at most 255 bytes is `Ok (len + 1, len)`
(above the bound the model panics in the `debug_assert!`). -/
theorem tls_vec.TlsByteVecU8.get_content_lengths_char (self : tls_vec.TlsByteVecU8)
    (h : self.vec.val.length ≤ 255) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU8.get_content_lengths self
    ⦃ ⇓ r => ⌜ ∃ a b : Std.Usize, r = .Ok (a, b) ∧ b.val = self.vec.val.length ∧
        a.val = self.vec.val.length + 1 ⌝ ⦄ := by
  unfold tls_vec.TlsByteVecU8.get_content_lengths
  simp only [deref_vec_ok, slice_iter_ok]
  erw [bind_tc_ok, bind_tc_ok]
  refine triple_bind_of_total (loop_len_sum_spec 1#usize _ 0#usize _ ?hlen ?hbody) ?hk
  case hlen => scalar_tac
  case hk =>
    rintro r ⟨v, rfl, hv⟩
    mvcgen [Copied.checked_len_add]
    all_goals simp_all [tryCF, core.num.U8.MAX, U8.rMax]
    all_goals scalar_tac
  case hbody =>
    intro it a ha
    mvcgen [core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
      Copied.U8.Insts.Tls_codecSize.tls_serialized_len, Copied.checked_len_add]
    all_goals (simp_all [tryCF, -List.length_eq_zero_iff]; try scalar_tac)

/-- `get_content_lengths` of a `TlsByteVecU8`, when it returns, is `Ok (len + 1, len)` and the length is within the prefix bound. -/
theorem tls_vec.TlsByteVecU8.get_content_lengths_partial (self : tls_vec.TlsByteVecU8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU8.get_content_lengths self
    ⦃ ⇓? r => ⌜ ∃ a b : Std.Usize, r = .Ok (a, b) ∧ b.val = self.vec.val.length ∧
        a.val = self.vec.val.length + 1 ∧ self.vec.val.length ≤ 255 ⌝ ⦄ := by
  unfold tls_vec.TlsByteVecU8.get_content_lengths
  simp only [deref_vec_ok, slice_iter_ok]
  erw [bind_tc_ok, bind_tc_ok]
  refine triple_bind_of_total (loop_len_sum_spec 1#usize _ 0#usize _ ?hlen ?hbody) ?hk
  case hlen => scalar_tac
  case hk =>
    rintro r ⟨v, rfl, hv⟩
    mvcgen [Copied.checked_len_add]
    all_goals simp_all [tryCF, core.num.U8.MAX, U8.rMax]
    all_goals scalar_tac
  case hbody =>
    intro it a ha
    mvcgen [core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
      Copied.U8.Insts.Tls_codecSize.tls_serialized_len, Copied.checked_len_add]
    all_goals (simp_all [tryCF, -List.length_eq_zero_iff]; try scalar_tac)

/-- `get_content_lengths` of a `TlsByteVecU16` of at most 65535 bytes is `Ok (len + 2, len)`
(above the bound the model panics in the `debug_assert!`). -/
theorem tls_vec.TlsByteVecU16.get_content_lengths_char (self : tls_vec.TlsByteVecU16)
    (h : self.vec.val.length ≤ 65535) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU16.get_content_lengths self
    ⦃ ⇓ r => ⌜ ∃ a b : Std.Usize, r = .Ok (a, b) ∧ b.val = self.vec.val.length ∧
        a.val = self.vec.val.length + 2 ⌝ ⦄ := by
  unfold tls_vec.TlsByteVecU16.get_content_lengths
  simp only [deref_vec_ok, slice_iter_ok]
  erw [bind_tc_ok, bind_tc_ok]
  refine triple_bind_of_total (loop_len_sum_spec 1#usize _ 0#usize _ ?hlen ?hbody) ?hk
  case hlen => scalar_tac
  case hk =>
    rintro r ⟨v, rfl, hv⟩
    mvcgen [Copied.checked_len_add]
    all_goals simp_all [tryCF, core.num.U16.MAX, U16.rMax]
    all_goals scalar_tac
  case hbody =>
    intro it a ha
    mvcgen [core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
      Copied.U8.Insts.Tls_codecSize.tls_serialized_len, Copied.checked_len_add]
    all_goals (simp_all [tryCF, -List.length_eq_zero_iff]; try scalar_tac)

/-- `get_content_lengths` of a `TlsByteVecU16`, when it returns, is `Ok (len + 2, len)` and the length is within the prefix bound. -/
theorem tls_vec.TlsByteVecU16.get_content_lengths_partial (self : tls_vec.TlsByteVecU16) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU16.get_content_lengths self
    ⦃ ⇓? r => ⌜ ∃ a b : Std.Usize, r = .Ok (a, b) ∧ b.val = self.vec.val.length ∧
        a.val = self.vec.val.length + 2 ∧ self.vec.val.length ≤ 65535 ⌝ ⦄ := by
  unfold tls_vec.TlsByteVecU16.get_content_lengths
  simp only [deref_vec_ok, slice_iter_ok]
  erw [bind_tc_ok, bind_tc_ok]
  refine triple_bind_of_total (loop_len_sum_spec 1#usize _ 0#usize _ ?hlen ?hbody) ?hk
  case hlen => scalar_tac
  case hk =>
    rintro r ⟨v, rfl, hv⟩
    mvcgen [Copied.checked_len_add]
    all_goals simp_all [tryCF, core.num.U16.MAX, U16.rMax]
    all_goals scalar_tac
  case hbody =>
    intro it a ha
    mvcgen [core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
      Copied.U8.Insts.Tls_codecSize.tls_serialized_len, Copied.checked_len_add]
    all_goals (simp_all [tryCF, -List.length_eq_zero_iff]; try scalar_tac)


/-- `get_content_lengths` of a `TlsByteVecU32` of at most 2^32 - 1 bytes and `len + 4` fits a `usize` is `Ok (len + 4, len)`
(above the bound the model panics in the `debug_assert!`). -/
theorem tls_vec.TlsByteVecU32.get_content_lengths_char (self : tls_vec.TlsByteVecU32)
    (h : self.vec.val.length ≤ 4294967295) (h' : self.vec.val.length + 4 ≤ Std.Usize.max) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU32.get_content_lengths self
    ⦃ ⇓ r => ⌜ ∃ a b : Std.Usize, r = .Ok (a, b) ∧ b.val = self.vec.val.length ∧
        a.val = self.vec.val.length + 4 ⌝ ⦄ := by
  unfold tls_vec.TlsByteVecU32.get_content_lengths
  simp only [deref_vec_ok, slice_iter_ok]
  erw [bind_tc_ok, bind_tc_ok]
  refine triple_bind_of_total (loop_len_sum_spec 1#usize _ 0#usize _ ?hlen ?hbody) ?hk
  case hlen => scalar_tac
  case hk =>
    rintro r ⟨v, rfl, hv⟩
    mvcgen [Copied.checked_len_add]
    all_goals simp_all [tryCF, core.num.U32.MAX, U32.rMax]
    all_goals scalar_tac
  case hbody =>
    intro it a ha
    mvcgen [core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
      Copied.U8.Insts.Tls_codecSize.tls_serialized_len, Copied.checked_len_add]
    all_goals (simp_all [tryCF, -List.length_eq_zero_iff]; try scalar_tac)

/-- `get_content_lengths` of a `TlsByteVecU32`, when it returns, is `Ok (len + 4, len)` and the length is within the prefix bound. -/
theorem tls_vec.TlsByteVecU32.get_content_lengths_partial (self : tls_vec.TlsByteVecU32) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU32.get_content_lengths self
    ⦃ ⇓? r => ⌜ ∃ a b : Std.Usize, r = .Ok (a, b) ∧ b.val = self.vec.val.length ∧
        a.val = self.vec.val.length + 4 ∧ self.vec.val.length ≤ 4294967295 ⌝ ⦄ := by
  unfold tls_vec.TlsByteVecU32.get_content_lengths
  simp only [deref_vec_ok, slice_iter_ok]
  erw [bind_tc_ok, bind_tc_ok]
  refine triple_bind_of_total (loop_len_sum_spec 1#usize _ 0#usize _ ?hlen ?hbody) ?hk
  case hlen => scalar_tac
  case hk =>
    rintro r ⟨v, rfl, hv⟩
    mvcgen [Copied.checked_len_add]
    all_goals simp_all [tryCF, core.num.U32.MAX, U32.rMax]
    all_goals scalar_tac
  case hbody =>
    intro it a ha
    mvcgen [core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
      Copied.U8.Insts.Tls_codecSize.tls_serialized_len, Copied.checked_len_add]
    all_goals (simp_all [tryCF, -List.length_eq_zero_iff]; try scalar_tac)


/-- `get_content_lengths` of a `TlsByteVecU24`, when it returns, is `Ok (len + 3, len)`. -/
theorem tls_vec.TlsByteVecU24.get_content_lengths_partial (self : tls_vec.TlsByteVecU24) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU24.get_content_lengths self
    ⦃ ⇓? r => ⌜ ∃ a b : Std.Usize, r = .Ok (a, b) ∧ b.val = self.vec.val.length ∧
        a.val = self.vec.val.length + 3 ⌝ ⦄ := by
  unfold tls_vec.TlsByteVecU24.get_content_lengths
  simp only [deref_vec_ok, slice_iter_ok]
  erw [bind_tc_ok, bind_tc_ok]
  refine triple_bind_of_total (loop_len_sum_spec 1#usize _ 0#usize _ ?hlen ?hbody) ?hk
  case hlen => scalar_tac
  case hk =>
    rintro r ⟨v, rfl, hv⟩
    simp only [Copied.Usize.Insts.CoreConvertFromU24_eq]
    mvcgen [Copied.checked_len_add,
      core.convert.TryFromTUInfallible.Blanket.try_from_Usize_U24_partial]
    all_goals (simp_all [tryCF]; try omega)
  case hbody =>
    intro it a ha
    mvcgen [core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
      Copied.U8.Insts.Tls_codecSize.tls_serialized_len, Copied.checked_len_add]
    all_goals (simp_all [tryCF, -List.length_eq_zero_iff]; try scalar_tac)

/-! ### `TlsByteVecU*::serialize_bytes_bytes` (uses the hand-written `get_content_lengths`)

`_partial`: if it returns `Ok out`, then `out` has the payload plus the prefix and the payload is within the
prefix bound (it panics above, in the model of the `debug_assert!`). `_char`: below the bound it does not panic. -/

/-- `TlsByteVecU8::deserialize_bytes_bytes` never panics; on success the remainder plus the
length prefix plus the payload is the input, and the payload is within the prefix bound. -/
theorem tls_vec.TlsByteVecU8.deserialize_char_le (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU8.deserialize_bytes_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : tls_vec.TlsByteVecU8) (t : Slice Std.U8), r = .Ok (v, t) →
        t.val.length + 1 + v.vec.val.length = bytes.val.length ∧
          v.vec.val.length ≤ 255 ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU8.deserialize_bytes_bytes, U8_deserialize_char,
    core.option.Option.ok_or_spec]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  · exact ⟨_, ‹_›⟩
  · rename_i r0 hP r1 p x1 r2 htf r3 hr3 o hca r4 hr4 cf1 val x2 o1 hget1 r5 hr5 cf2 val1 x3
      vec hvec o2 hget2 r6 hr6 cf3 val2 x4 e0 e1 e2 e3
    intro v t h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (core.result.Result.Ok.inj h)
    have hl : 1 ≤ bytes.val.length := by
      by_contra hn
      rw [hP.2 (by omega)] at e0
      cases e0
    obtain ⟨a, tt, _, htt, hr⟩ := hP.1 hl
    rw [hr] at e0
    have hp := core.result.Result.Ok.inj e0
    have hpt : p.2 = tt := by rw [← hp]
    have hp2 : p.2.val.length = bytes.val.length - 1 := by rw [hpt, htt]; simp
    have h1 := hget1 val1 (ok_or_eq_ok hr5 e2)
    have h2 : val.val = r3.val + 1 := by
      by_cases hov : r3.val + (1#usize).val ≤ Usize.max
      · obtain ⟨z, hz1, hz2⟩ := hca.1 hov
        rw [hz1] at hr4
        have := core.result.Result.Ok.inj (hr4.symm.trans e1)
        subst this
        simpa using hz2
      · have := hca.2 (by omega)
        rw [this] at hr4
        rw [hr4] at e1
        cases e1
    have ho2 := ok_or_eq_ok hr6 e3
    have hle : r3.val ≤ p.2.val.length := by
      by_contra hn
      rw [hget2.2 (by omega)] at ho2
      cases ho2
    obtain ⟨t2, ht2, ht2'⟩ := hget2.1 hle
    rw [ht2] at ho2
    have hv2 := Option.some.inj ho2
    subst hv2
    have h3 : t2.val.length = p.2.val.length - r3.val := by rw [ht2']; simp
    subst hvec
    show t2.val.length + 1 + vec.val.length = bytes.val.length ∧ vec.val.length ≤ 255
    have hone : (1#usize).val = 1 := rfl
    have hc := core.result.Result.Ok.inj (hr3.symm.trans htf)
    have hb : r3.val ≤ 255 := by rw [hc]; scalar_tac
    omega
  · intro _ v t h; cases h
  · intro _ v t h; cases h
  · intro _ v t h; cases h
  · intro _ v t h; cases h

/-- `TlsByteVecU16::deserialize_bytes_bytes` never panics; on success the remainder plus the
length prefix plus the payload is the input, and the payload is within the prefix bound. -/
theorem tls_vec.TlsByteVecU16.deserialize_char_le (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU16.deserialize_bytes_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : tls_vec.TlsByteVecU16) (t : Slice Std.U8), r = .Ok (v, t) →
        t.val.length + 2 + v.vec.val.length = bytes.val.length ∧
          v.vec.val.length ≤ 65535 ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU16.deserialize_bytes_bytes, U16_deserialize_char,
    core.option.Option.ok_or_spec]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  · exact ⟨_, ‹_›⟩
  · rename_i r0 hP r1 p x1 r2 htf r3 hr3 o hca r4 hr4 cf1 val x2 o1 hget1 r5 hr5 cf2 val1 x3
      vec hvec o2 hget2 r6 hr6 cf3 val2 x4 e0 e1 e2 e3
    intro v t h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (core.result.Result.Ok.inj h)
    have hl : 2 ≤ bytes.val.length := by
      by_contra hn
      rw [hP.2 (by omega)] at e0
      cases e0
    obtain ⟨a, tt, _, htt, hr⟩ := hP.1 hl
    rw [hr] at e0
    have hp := core.result.Result.Ok.inj e0
    have hpt : p.2 = tt := by rw [← hp]
    have hp2 : p.2.val.length = bytes.val.length - 2 := by rw [hpt, htt]; simp
    have h1 := hget1 val1 (ok_or_eq_ok hr5 e2)
    have h2 : val.val = r3.val + 2 := by
      by_cases hov : r3.val + (2#usize).val ≤ Usize.max
      · obtain ⟨z, hz1, hz2⟩ := hca.1 hov
        rw [hz1] at hr4
        have := core.result.Result.Ok.inj (hr4.symm.trans e1)
        subst this
        simpa using hz2
      · have := hca.2 (by omega)
        rw [this] at hr4
        rw [hr4] at e1
        cases e1
    have ho2 := ok_or_eq_ok hr6 e3
    have hle : r3.val ≤ p.2.val.length := by
      by_contra hn
      rw [hget2.2 (by omega)] at ho2
      cases ho2
    obtain ⟨t2, ht2, ht2'⟩ := hget2.1 hle
    rw [ht2] at ho2
    have hv2 := Option.some.inj ho2
    subst hv2
    have h3 : t2.val.length = p.2.val.length - r3.val := by rw [ht2']; simp
    subst hvec
    show t2.val.length + 2 + vec.val.length = bytes.val.length ∧ vec.val.length ≤ 65535
    have hone : (2#usize).val = 2 := rfl
    have hc := core.result.Result.Ok.inj (hr3.symm.trans htf)
    have hb : r3.val ≤ 65535 := by rw [hc]; scalar_tac
    omega
  · intro _ v t h; cases h
  · intro _ v t h; cases h
  · intro _ v t h; cases h
  · intro _ v t h; cases h

/-- `TlsByteVecU32::deserialize_bytes_bytes` never panics; on success the remainder plus the
length prefix plus the payload is the input, and the payload is within the prefix bound. -/
theorem tls_vec.TlsByteVecU32.deserialize_char_le (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU32.deserialize_bytes_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : tls_vec.TlsByteVecU32) (t : Slice Std.U8), r = .Ok (v, t) →
        t.val.length + 4 + v.vec.val.length = bytes.val.length ∧
          v.vec.val.length ≤ 4294967295 ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU32.deserialize_bytes_bytes, U32_deserialize_char,
    core.option.Option.ok_or_spec]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  · exact ⟨_, ‹_›⟩
  · rename_i r0 hP r1 p x1 r2 htf r3 hr3 o hca r4 hr4 cf1 val x2 o1 hget1 r5 hr5 cf2 val1 x3
      vec hvec o2 hget2 r6 hr6 cf3 val2 x4 e0 e1 e2 e3
    intro v t h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (core.result.Result.Ok.inj h)
    have hl : 4 ≤ bytes.val.length := by
      by_contra hn
      rw [hP.2 (by omega)] at e0
      cases e0
    obtain ⟨a, tt, _, htt, hr⟩ := hP.1 hl
    rw [hr] at e0
    have hp := core.result.Result.Ok.inj e0
    have hpt : p.2 = tt := by rw [← hp]
    have hp2 : p.2.val.length = bytes.val.length - 4 := by rw [hpt, htt]; simp
    have h1 := hget1 val1 (ok_or_eq_ok hr5 e2)
    have h2 : val.val = r3.val + 4 := by
      by_cases hov : r3.val + (4#usize).val ≤ Usize.max
      · obtain ⟨z, hz1, hz2⟩ := hca.1 hov
        rw [hz1] at hr4
        have := core.result.Result.Ok.inj (hr4.symm.trans e1)
        subst this
        simpa using hz2
      · have := hca.2 (by omega)
        rw [this] at hr4
        rw [hr4] at e1
        cases e1
    have ho2 := ok_or_eq_ok hr6 e3
    have hle : r3.val ≤ p.2.val.length := by
      by_contra hn
      rw [hget2.2 (by omega)] at ho2
      cases ho2
    obtain ⟨t2, ht2, ht2'⟩ := hget2.1 hle
    rw [ht2] at ho2
    have hv2 := Option.some.inj ho2
    subst hv2
    have h3 : t2.val.length = p.2.val.length - r3.val := by rw [ht2']; simp
    subst hvec
    show t2.val.length + 4 + vec.val.length = bytes.val.length ∧ vec.val.length ≤ 4294967295
    have hone : (4#usize).val = 4 := rfl
    have hc := core.result.Result.Ok.inj (hr3.symm.trans htf)
    have hb : r3.val ≤ 4294967295 := by rw [hc]; scalar_tac
    omega
  · intro _ v t h; cases h
  · intro _ v t h; cases h
  · intro _ v t h; cases h
  · intro _ v t h; cases h

/-- `saturating_add` does not saturate when the sum fits. -/
theorem Usize_saturating_add_val_le (x y : Std.Usize) (h : x.val + y.val ≤ Std.Usize.max) :
    (UScalar.saturating_add x y).val = x.val + y.val := by
  have hm : x.val + y.val ≤ UScalar.max UScalarTy.Usize := by
    simp only [UScalar.max, UScalarTy.numBits]
    simpa [Std.Usize.max, UScalar.max, UScalarTy.numBits, Std.Usize.numBits] using h
  have hlt : x.val + y.val < 2 ^ System.Platform.numBits := by
    simp only [UScalar.max, UScalarTy.numBits] at hm
    have := Nat.one_le_two_pow (n := System.Platform.numBits)
    omega
  unfold UScalar.saturating_add
  rw [min_eq_right hm]
  unfold UScalar.val
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hlt

/-- `checked_alloc_len` of operands whose sum fits a `usize`: the sum, or an error. -/
theorem checked_alloc_len_total (a b : Std.Usize) (h : a.val + b.val ≤ Std.Usize.max) :
    ⦃ ⌜ True ⌝ ⦄ checked_alloc_len a b
    ⦃ ⇓ r => ⌜ (∃ n : Std.Usize, r = .Ok n ∧ n.val = a.val + b.val) ∨ ∃ e, r = .Err e ⌝ ⦄ := by
  have hs := Usize_saturating_add_val_le a b h
  mvcgen [checked_alloc_len, checked_capacity, CoreModels.core.num.Usize.saturating_add_spec]
  · exact Or.inr ⟨_, rfl⟩
  · rename_i sat hsat hle
    subst hsat
    exact Or.inl ⟨_, rfl, hs⟩

/-- `Vec::<u8>::extend_from_slice` appends the slice, given room. -/
theorem alloc.vec.Vec.extend_from_slice_U8_spec (v : alloc.vec.Vec Std.U8) (s : Slice Std.U8)
    (h : (v : Slice Std.U8).val.length + s.val.length ≤ Usize.max) :
    ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.extend_from_slice core.U8.Insts.CoreCloneClone v s
    ⦃ ⇓ r => ⌜ (r : Slice Std.U8).val = (v : Slice Std.U8).val ++ s.val ⌝ ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice rust_primitives.sequence.seq_extend
  erw [mapM_clone_U8]
  have hh : (v : Slice Std.U8).val.length + s.val.length ≤ Usize.max := h
  mvcgen
  all_goals (exfalso; simp_all +zetaDelta [List.length_append])

/-- `Result::unwrap`, when it returns, was given an `Ok`. -/
theorem core.result.Result.unwrap_partial {T E : Type} (fmtDebugInst : core.fmt.Debug E)
    (x : core.result.Result T E) :
    ⦃ ⌜ True ⌝ ⦄ core.result.Result.unwrap fmtDebugInst x ⦃ ⇓? r => ⌜ x = .Ok r ⌝ ⦄ := by
  apply partial_triple_of_ok
  intro r hr
  cases x with
  | Ok t => unfold core.result.Result.unwrap at hr; simp at hr; subst hr; rfl
  | Err e => unfold core.result.Result.unwrap core.panicking.internal.panic at hr; simp at hr

/-- `U24::try_from(usize)` returns (partial: only used to sequence). -/
theorem U24.Insts.CoreConvertTryFromUsizeError.try_from_partial (x : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ U24.Insts.CoreConvertTryFromUsizeError.try_from x ⦃ ⇓? _ => ⌜ True ⌝ ⦄ :=
  partial_triple_of_ok (fun _ _ => trivial)

/-- `usize -> u8` `TryFrom`: `Ok` of the cast when it fits, an error otherwise. -/
theorem core.U8.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from_char (x : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ core.U8.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from x
    ⦃ ⇓ r => ⌜ (x.val ≤ 255 → ∃ y : Std.U8, r = .Ok y ∧ y.val = x.val) ∧
        (255 < x.val → ∃ e, r = .Err e) ⌝ ⦄ := by
  unfold core.U8.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from
  mvcgen
  all_goals (subst_vars; simp [core.num.U8.MAX, core.num.U8.MIN, U8.rMax] at *; try scalar_tac)

/-- `TlsByteVecU8::assert_written_bytes` never panics (relies on the ASSUMED fmt no-fail axioms). -/
theorem tls_vec.TlsByteVecU8.assert_written_bytes_total (self : tls_vec.TlsByteVecU8)
    (tls_serialized_len written : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU8.assert_written_bytes self tls_serialized_len written
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU8.assert_written_bytes]

/-- `usize -> u16` `TryFrom`: `Ok` of the cast when it fits, an error otherwise. -/
theorem core.U16.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from_char (x : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ core.U16.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from x
    ⦃ ⇓ r => ⌜ (x.val ≤ 65535 → ∃ y : Std.U16, r = .Ok y ∧ y.val = x.val) ∧
        (65535 < x.val → ∃ e, r = .Err e) ⌝ ⦄ := by
  unfold core.U16.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from
  mvcgen
  all_goals (subst_vars; simp [core.num.U16.MAX, core.num.U16.MIN, U16.rMax] at *; try scalar_tac)

/-- `TlsByteVecU16::assert_written_bytes` never panics (relies on the ASSUMED fmt no-fail axioms). -/
theorem tls_vec.TlsByteVecU16.assert_written_bytes_total (self : tls_vec.TlsByteVecU16)
    (tls_serialized_len written : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU16.assert_written_bytes self tls_serialized_len written
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU16.assert_written_bytes]

/-- `usize -> u32` `TryFrom`: `Ok` of the cast when it fits, an error otherwise. -/
theorem core.U32.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from_char (x : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ core.U32.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from x
    ⦃ ⇓ r => ⌜ (x.val ≤ 4294967295 → ∃ y : Std.U32, r = .Ok y ∧ y.val = x.val) ∧
        (4294967295 < x.val → ∃ e, r = .Err e) ⌝ ⦄ := by
  unfold core.U32.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from
  mvcgen
  all_goals (subst_vars; simp [core.num.U32.MAX, core.num.U32.MIN, U32.rMax] at *; try scalar_tac)

/-- `TlsByteVecU32::assert_written_bytes` never panics (relies on the ASSUMED fmt no-fail axioms). -/
theorem tls_vec.TlsByteVecU32.assert_written_bytes_total (self : tls_vec.TlsByteVecU32)
    (tls_serialized_len written : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU32.assert_written_bytes self tls_serialized_len written
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU32.assert_written_bytes]

/-- `TlsByteVecU24::assert_written_bytes` never panics (relies on the ASSUMED fmt no-fail axioms). -/
theorem tls_vec.TlsByteVecU24.assert_written_bytes_total (self : tls_vec.TlsByteVecU24)
    (tls_serialized_len written : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU24.assert_written_bytes self tls_serialized_len written
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU24.assert_written_bytes]

/-- `TlsByteVecU8::serialize_bytes_bytes`, when it returns `Ok`, gives the payload plus the 1-byte prefix, and the payload is within the prefix bound. -/
theorem tls_vec.TlsByteVecU8.serialize_bytes_bytes_partial (self : tls_vec.TlsByteVecU8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU8.serialize_bytes_bytes self
    ⦃ ⇓? r => ⌜ ∀ out : alloc.vec.Vec Std.U8, r = .Ok out →
        out.val.length = self.vec.val.length + 1 ∧ self.vec.val.length ≤ 255 ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU8.serialize_bytes_bytes,
    tls_vec.TlsByteVecU8.get_content_lengths_partial,
    checked_alloc_len_total, alloc.vec.Vec.extend_from_slice_U8_spec,
    core.U8.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from_char,
    alloc.vec.Vec.with_capacity, core.result.Result.unwrap_ok_spec, U8_serialize_char,
    alloc.vec.Vec.len_spec, tls_vec.TlsByteVecU8.as_slice, CoreModels.core.slice.Slice.len_spec,
    tls_vec.TlsByteVecU8.assert_written_bytes_total]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  all_goals (try casesm* (∃ _, _), (_ ∧ _))
  all_goals subst_vars
  all_goals (simp_all [Slice.len, Slice.new])
  all_goals first
    | omega
    | scalar_tac
    | (obtain ⟨y, hy, -⟩ := ‹∃ y, _ = _ ∧ _›; exact ⟨y, hy⟩)
    | (intro _ out h; cases h)

/-- `TlsByteVecU8::serialize_bytes_bytes` of a vector within the prefix bound does not panic; an `Ok` result has the payload length plus the 1-byte prefix. -/
theorem tls_vec.TlsByteVecU8.serialize_bytes_bytes_char (self : tls_vec.TlsByteVecU8)
    (h : self.vec.val.length ≤ 255) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU8.serialize_bytes_bytes self
    ⦃ ⇓ r => ⌜ ∀ out : alloc.vec.Vec Std.U8, r = .Ok out →
        out.val.length = self.vec.val.length + 1 ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU8.serialize_bytes_bytes,
    tls_vec.TlsByteVecU8.get_content_lengths_char,
    checked_alloc_len_total, alloc.vec.Vec.extend_from_slice_U8_spec,
    core.U8.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from_char,
    alloc.vec.Vec.with_capacity, core.result.Result.unwrap_ok_spec, U8_serialize_char,
    alloc.vec.Vec.len_spec, tls_vec.TlsByteVecU8.as_slice, CoreModels.core.slice.Slice.len_spec,
    tls_vec.TlsByteVecU8.assert_written_bytes_total]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  all_goals (try casesm* (∃ _, _), (_ ∧ _))
  all_goals subst_vars
  all_goals (simp_all [Slice.len, Slice.new])
  all_goals first
    | omega
    | scalar_tac
    | (obtain ⟨y, hy, -⟩ := ‹∃ y, _ = _ ∧ _›; exact ⟨y, hy⟩)
    | (intro _ out h; cases h)

/-- `TlsByteVecU16::serialize_bytes_bytes`, when it returns `Ok`, gives the payload plus the 2-byte prefix, and the payload is within the prefix bound. -/
theorem tls_vec.TlsByteVecU16.serialize_bytes_bytes_partial (self : tls_vec.TlsByteVecU16) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU16.serialize_bytes_bytes self
    ⦃ ⇓? r => ⌜ ∀ out : alloc.vec.Vec Std.U8, r = .Ok out →
        out.val.length = self.vec.val.length + 2 ∧ self.vec.val.length ≤ 65535 ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU16.serialize_bytes_bytes,
    tls_vec.TlsByteVecU16.get_content_lengths_partial,
    checked_alloc_len_total, alloc.vec.Vec.extend_from_slice_U8_spec,
    core.U16.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from_char,
    alloc.vec.Vec.with_capacity, core.result.Result.unwrap_ok_spec, U16_serialize_char,
    alloc.vec.Vec.len_spec, tls_vec.TlsByteVecU16.as_slice, CoreModels.core.slice.Slice.len_spec,
    tls_vec.TlsByteVecU16.assert_written_bytes_total]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  all_goals (try casesm* (∃ _, _), (_ ∧ _))
  all_goals subst_vars
  all_goals (simp_all [Slice.len, Slice.new])
  all_goals first
    | omega
    | scalar_tac
    | (obtain ⟨y, hy, -⟩ := ‹∃ y, _ = _ ∧ _›; exact ⟨y, hy⟩)
    | (intro _ out h; cases h)

/-- `TlsByteVecU16::serialize_bytes_bytes` of a vector within the prefix bound does not panic; an `Ok` result has the payload length plus the 2-byte prefix. -/
theorem tls_vec.TlsByteVecU16.serialize_bytes_bytes_char (self : tls_vec.TlsByteVecU16)
    (h : self.vec.val.length ≤ 65535) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU16.serialize_bytes_bytes self
    ⦃ ⇓ r => ⌜ ∀ out : alloc.vec.Vec Std.U8, r = .Ok out →
        out.val.length = self.vec.val.length + 2 ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU16.serialize_bytes_bytes,
    tls_vec.TlsByteVecU16.get_content_lengths_char,
    checked_alloc_len_total, alloc.vec.Vec.extend_from_slice_U8_spec,
    core.U16.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from_char,
    alloc.vec.Vec.with_capacity, core.result.Result.unwrap_ok_spec, U16_serialize_char,
    alloc.vec.Vec.len_spec, tls_vec.TlsByteVecU16.as_slice, CoreModels.core.slice.Slice.len_spec,
    tls_vec.TlsByteVecU16.assert_written_bytes_total]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  all_goals (try casesm* (∃ _, _), (_ ∧ _))
  all_goals subst_vars
  all_goals (simp_all [Slice.len, Slice.new])
  all_goals first
    | omega
    | scalar_tac
    | (obtain ⟨y, hy, -⟩ := ‹∃ y, _ = _ ∧ _›; exact ⟨y, hy⟩)
    | (intro _ out h; cases h)

/-- `TlsByteVecU24::serialize_bytes_bytes`, when it returns `Ok`, gives the payload plus the 3-byte prefix (partial: `usize::from(U24)` may panic on 32-bit `usize`). -/
theorem tls_vec.TlsByteVecU24.serialize_bytes_bytes_partial (self : tls_vec.TlsByteVecU24) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU24.serialize_bytes_bytes self
    ⦃ ⇓? r => ⌜ ∀ out : alloc.vec.Vec Std.U8, r = .Ok out →
        out.val.length = self.vec.val.length + 3 ⌝ ⦄ := by
  mvcgen [-core.result.Result.unwrap_ok_spec, tls_vec.TlsByteVecU24.serialize_bytes_bytes,
    tls_vec.TlsByteVecU24.get_content_lengths_partial,
    checked_alloc_len_total, alloc.vec.Vec.extend_from_slice_U8_spec,
    U24.Insts.CoreConvertTryFromUsizeError.try_from_partial,
    alloc.vec.Vec.with_capacity, core.result.Result.unwrap_partial, U24_serialize_char,
    alloc.vec.Vec.len_spec, tls_vec.TlsByteVecU24.as_slice, CoreModels.core.slice.Slice.len_spec,
    tls_vec.TlsByteVecU24.assert_written_bytes_total]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  all_goals (try casesm* (∃ _, _), (_ ∧ _))
  all_goals subst_vars
  all_goals (simp_all [Slice.len, Slice.new])

  all_goals first
    | omega
    | scalar_tac
    | (obtain ⟨y, hy, -⟩ := ‹∃ y, _ = _ ∧ _›; exact ⟨y, hy⟩)
    | (intro _ out h; cases h)

/-- `TlsByteVecU32::serialize_bytes_bytes`, when it returns `Ok`, gives the payload plus the 4-byte prefix, and the payload is within the prefix bound. -/
theorem tls_vec.TlsByteVecU32.serialize_bytes_bytes_partial (self : tls_vec.TlsByteVecU32) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU32.serialize_bytes_bytes self
    ⦃ ⇓? r => ⌜ ∀ out : alloc.vec.Vec Std.U8, r = .Ok out →
        out.val.length = self.vec.val.length + 4 ∧ self.vec.val.length ≤ 4294967295 ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU32.serialize_bytes_bytes,
    tls_vec.TlsByteVecU32.get_content_lengths_partial,
    checked_alloc_len_total, alloc.vec.Vec.extend_from_slice_U8_spec,
    core.U32.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from_char,
    alloc.vec.Vec.with_capacity, core.result.Result.unwrap_ok_spec, U32_serialize_char,
    alloc.vec.Vec.len_spec, tls_vec.TlsByteVecU32.as_slice, CoreModels.core.slice.Slice.len_spec,
    tls_vec.TlsByteVecU32.assert_written_bytes_total]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  all_goals (try casesm* (∃ _, _), (_ ∧ _))
  all_goals subst_vars
  all_goals (simp_all [Slice.len, Slice.new])
  all_goals first
    | omega
    | scalar_tac
    | (obtain ⟨y, hy, -⟩ := ‹∃ y, _ = _ ∧ _›; exact ⟨y, hy⟩)
    | (intro _ out h; cases h)

/-- `TlsByteVecU32::serialize_bytes_bytes` of a vector within the prefix bound does not panic; an `Ok` result has the payload length plus the 4-byte prefix. -/
theorem tls_vec.TlsByteVecU32.serialize_bytes_bytes_char (self : tls_vec.TlsByteVecU32)
    (h : self.vec.val.length ≤ 4294967295)
    (h' : self.vec.val.length + 4 ≤ Std.Usize.max) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU32.serialize_bytes_bytes self
    ⦃ ⇓ r => ⌜ ∀ out : alloc.vec.Vec Std.U8, r = .Ok out →
        out.val.length = self.vec.val.length + 4 ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU32.serialize_bytes_bytes,
    tls_vec.TlsByteVecU32.get_content_lengths_char,
    checked_alloc_len_total, alloc.vec.Vec.extend_from_slice_U8_spec,
    core.U32.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from_char,
    alloc.vec.Vec.with_capacity, core.result.Result.unwrap_ok_spec, U32_serialize_char,
    alloc.vec.Vec.len_spec, tls_vec.TlsByteVecU32.as_slice, CoreModels.core.slice.Slice.len_spec,
    tls_vec.TlsByteVecU32.assert_written_bytes_total]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  all_goals (try casesm* (∃ _, _), (_ ∧ _))
  all_goals subst_vars
  all_goals (simp_all [Slice.len, Slice.new])
  all_goals first
    | omega
    | scalar_tac
    | (obtain ⟨y, hy, -⟩ := ‹∃ y, _ = _ ∧ _›; exact ⟨y, hy⟩)
    | (intro _ out h; cases h)

/-- `TlsByteVecU8::serialize_bytes_bytes`, when it returns `Ok`, gives the 1-byte length prefix followed by the payload. -/
theorem tls_vec.TlsByteVecU8.serialize_bytes_bytes_content (self : tls_vec.TlsByteVecU8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU8.serialize_bytes_bytes self
    ⦃ ⇓? r => ⌜ ∀ out : alloc.vec.Vec Std.U8, r = .Ok out →
        ∃ n : Std.U8, n.val = self.vec.val.length ∧ out.val = n :: self.vec.val ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU8.serialize_bytes_bytes,
    tls_vec.TlsByteVecU8.get_content_lengths_partial,
    checked_alloc_len_total, alloc.vec.Vec.extend_from_slice_U8_spec,
    core.U8.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from_char,
    alloc.vec.Vec.with_capacity, core.result.Result.unwrap_ok_spec, U8_serialize_char,
    alloc.vec.Vec.len_spec, tls_vec.TlsByteVecU8.as_slice, CoreModels.core.slice.Slice.len_spec,
    tls_vec.TlsByteVecU8.assert_written_bytes_total]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  all_goals (try casesm* (∃ _, _), (_ ∧ _))
  all_goals subst_vars
  all_goals (simp_all [Slice.len, Slice.new])
  all_goals first
    | omega
    | scalar_tac
    | (obtain ⟨y, hy, -⟩ := ‹∃ y, _ = _ ∧ _›; exact ⟨y, hy⟩)
    | (rw [U8_to_be_bytes_val]; exact ⟨_, ‹_›, rfl⟩)
    | (intro _ out h; cases h)

/-- `s.get(start..end)`, content version: if it returns `Some t`, then `t` is the corresponding sublist. -/
theorem core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_content_spec
    {T : Type} (r : core.ops.range.Range Std.Usize) (s : Slice T) :
    ⦃ ⌜ True ⌝ ⦄ core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get r s
    ⦃ ⇓ o => ⌜ ∀ t, o = some t → r.start.val ≤ r.end.val ∧ r.end.val ≤ s.val.length ∧
        t.val = (s.val.drop r.start.val).take (r.end.val - r.start.val) ⌝ ⦄ := by
  unfold core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get
    rust_primitives.slice.slice_length rust_primitives.slice.slice_slice Slice.subslice
  mvcgen
  · rename_i h1 h2 h3
    have hl : (s.len).val = s.val.length := by simp
    intro t ht
    have ht' := Option.some.inj ht
    subst ht'
    refine ⟨h3.1, h3.2, ?_⟩
    simp [List.slice]
  · rename_i h1 h2 h3
    have hl : (s.len).val = s.val.length := by simp
    exact absurd ⟨by scalar_tac, by scalar_tac⟩ h3
  · intro t ht; cases ht
  · intro t ht; cases ht

/-- `TlsByteVecU8::deserialize_bytes_bytes` never panics; on success the input is the 1-byte length prefix, the payload, then the remainder. -/
theorem tls_vec.TlsByteVecU8.deserialize_content (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU8.deserialize_bytes_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : tls_vec.TlsByteVecU8) (t : Slice Std.U8), r = .Ok (v, t) →
        ∃ n : Std.U8, n.val = v.vec.val.length ∧ bytes.val = n :: (v.vec.val ++ t.val) ⌝ ⦄ := by
  mvcgen [-core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_some_spec,
    tls_vec.TlsByteVecU8.deserialize_bytes_bytes, U8_deserialize_char,
    core.option.Option.ok_or_spec,
    core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_content_spec]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  · exact ⟨_, ‹_›⟩
  · rename_i r0 hP r1 p x1 r2 htf r3 hr3 o hca r4 hr4 cf1 val x2 o1 hget1 r5 hr5 cf2 val1 x3
      vec hvec o2 hget2 r6 hr6 cf3 val2 x4 e0 e1 e2 e3
    intro v t h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (core.result.Result.Ok.inj h)
    have hl : 1 ≤ bytes.val.length := by
      by_contra hn
      rw [hP.2 (by omega)] at e0
      cases e0
    obtain ⟨a, tt, ha, htt, hr⟩ := hP.1 hl
    rw [hr] at e0
    have hp := core.result.Result.Ok.inj e0
    have hpt : p.2 = tt := by rw [← hp]
    have hpp : p.1 = Aeneas.Std.core.num.U8.from_be_bytes a := by rw [← hp]
    have h1 := hget1 val1 (ok_or_eq_ok hr5 e2)
    have h2 : val.val = r3.val + 1 := by
      by_cases hov : r3.val + (1#usize).val ≤ Usize.max
      · obtain ⟨z, hz1, hz2⟩ := hca.1 hov
        rw [hz1] at hr4
        have := core.result.Result.Ok.inj (hr4.symm.trans e1)
        subst this
        simpa using hz2
      · have := hca.2 (by omega)
        rw [this] at hr4
        rw [hr4] at e1
        cases e1
    have ho2 := ok_or_eq_ok hr6 e3
    have hle : r3.val ≤ p.2.val.length := by
      by_contra hn
      rw [hget2.2 (by omega)] at ho2
      cases ho2
    obtain ⟨t2, ht2, ht2'⟩ := hget2.1 hle
    rw [ht2] at ho2
    have hv2 := Option.some.inj ho2
    subst hv2
    subst hvec
    have hc := core.result.Result.Ok.inj (hr3.symm.trans htf)
    have hone : (1#usize).val = 1 := rfl
    have hb : r3.val = p.1.val := by rw [hc]; simp
    have ha1 : a.val = [p.1] := by
      have := U8_to_be_bytes_from_be_bytes a
      rw [← hpp] at this
      rw [← this, U8_to_be_bytes_val]
    have hba : bytes.val = a.val ++ tt.val := by
      rw [ha, htt, List.take_append_drop]
    have hv : vec.val = tt.val.take r3.val := by
      have : val.val - (1#usize).val = r3.val := by omega
      rw [h1.2.2, this, htt, hone]
    have ht : t2.val = tt.val.drop r3.val := by rw [ht2', hpt]
    refine ⟨p.1, ?_, ?_⟩
    · rw [hv]
      have : tt.val.length = bytes.val.length - 1 := by rw [htt]; simp
      simp only [List.length_take]
      omega
    · show bytes.val = p.1 :: (vec.val ++ t2.val)
      rw [hba, ha1, hv, ht, List.take_append_drop]
      rfl
  · intro _ v t h; cases h
  · intro _ v t h; cases h
  · intro _ v t h; cases h
  · intro _ v t h; cases h

/-- `Vec::eq` (element-wise, through a spec of the element `eq`): `decide` of list equality. -/
theorem alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq_spec {T : Type} [DecidableEq T]
    (inst : core.cmp.PartialEq T T) (a b : alloc.vec.Vec T)
    (heq : ∀ x y, ⦃ ⌜ True ⌝ ⦄ inst.eq x y ⦃ ⇓ r => ⌜ r = decide (x = y) ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq inst a b
    ⦃ ⇓ r => ⌜ r = decide (a.val = b.val) ⌝ ⦄ := by
  have hbody : ∀ (it : core.ops.range.Range Std.Usize) (res : Bool),
      it.end.val = a.val.length → a.val.length = b.val.length →
      it.start.val ≤ it.end.val → (res = true ↔ ∀ j, j < it.start.val → a.val[j]? = b.val[j]?) →
      ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq_loop.body inst a b it res
      ⦃ ⇓ r => ⌜ match r with
        | .done y => y = decide (a.val = b.val)
        | .cont (it', res') => (it'.end.val = a.val.length ∧ it'.start.val ≤ it'.end.val ∧
            (res' = true ↔ ∀ j, j < it'.start.val → a.val[j]? = b.val[j]?)) ∧
            it'.end.val - it'.start.val < it.end.val - it.start.val ⌝ ⦄ := by
    intro it res hend hlen hle hres
    unfold alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq_loop.body
    mvcgen [heq, core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next_Usize_spec]
    · -- exhausted range
      rename_i r hr hnx
      by_cases hlt : it.start.val < it.end.val
      · rw [(hnx.1 hlt).1] at hr; simp at hr
      · have hse : it.start.val = it.end.val := by omega
        rcases Bool.eq_false_or_eq_true res with hr1 | hr1
        · rw [hr1]
          have hall := hres.mp hr1
          simp only [true_eq_decide_iff]
          apply List.ext_getElem?
          intro j
          by_cases hj : j < it.start.val
          · exact hall j hj
          · rw [List.getElem?_eq_none_iff.mpr (by omega), List.getElem?_eq_none_iff.mpr (by omega)]
        · rw [hr1]
          simp only [false_eq_decide_iff]
          intro hab'
          have : res = true := by
            apply hres.mpr; intro j _; rw [hab']
          rw [hr1] at this; simp at this
    · rename_i r i hi hres1 hnx
      obtain ⟨hlt, hii, hs, he⟩ := core.ops.range.Range.next_Usize_some it r i hi hnx
      subst hii
      omega
    · rename_i r i hi hres1 hnx x hx
      obtain ⟨hlt, hii, hs, he⟩ := core.ops.range.Range.next_Usize_some it r i hi hnx
      subst hii
      omega
    · rename_i r i hi hres1 hnx x hx y hy c hc hdec
      obtain ⟨hlt, hii, hs, he⟩ := core.ops.range.Range.next_Usize_some it r i hi hnx
      subst hii
      have he' : r.2.end.val = it.end.val := by rw [he]
      have hxy : x = y := by subst hc; simpa using hdec.symm
      have hall := hres.mp hres1
      refine ⟨⟨by omega, by omega, ⟨fun _ j hj => ?_, fun _ => trivial⟩⟩, by omega⟩
      by_cases hji : j < it.start.val
      · exact hall j hji
      · have hj : j = it.start.val := by omega
        subst hj
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
        simp only [Option.some.injEq]
        rw [← hx, ← hy]; exact hxy
    · rename_i r i hi hres1 hnx x hx y hy c hc hdec
      obtain ⟨hlt, hii, hs, he⟩ := core.ops.range.Range.next_Usize_some it r i hi hnx
      subst hii
      have he' : r.2.end.val = it.end.val := by rw [he]
      have hne : x ≠ y := by
        intro hxy; apply hc; rw [hdec]; simp [hxy]
      refine ⟨⟨by omega, by omega, ⟨fun h => absurd h (by simp), fun hall => ?_⟩⟩, by omega⟩
      exfalso
      have := hall it.start.val (by omega)
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at this
      apply hne
      have h2 := Option.some.inj this
      rw [hx, hy]; exact h2
    · rename_i r i hi hres1 hnx
      obtain ⟨hlt, hii, hs, he⟩ := core.ops.range.Range.next_Usize_some it r i hi hnx
      subst hii
      have he' : r.2.end.val = it.end.val := by rw [he]
      refine ⟨⟨by omega, by omega, ⟨fun h => absurd h (by simp), fun hall => ?_⟩⟩, by omega⟩
      exfalso
      apply hres1
      apply hres.mpr
      intro j hj
      exact hall j (by omega)
  have hloop : ∀ (it : core.ops.range.Range Std.Usize) (res : Bool),
      it.end.val = a.val.length → a.val.length = b.val.length →
      it.start.val ≤ it.end.val → (res = true ↔ ∀ j, j < it.start.val → a.val[j]? = b.val[j]?) →
      ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq_loop inst it a b res
      ⦃ ⇓ r => ⌜ r = decide (a.val = b.val) ⌝ ⦄ := by
    intro it res hend hlen hle hres
    unfold alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq_loop
    apply Aeneas.Std.WP.spec_to_mvcgen
    apply Aeneas.Std.loop.spec_decr_nat
      (fun p : core.ops.range.Range Std.Usize × Bool => p.1.end.val - p.1.start.val)
      (fun p : core.ops.range.Range Std.Usize × Bool => p.1.end.val = a.val.length ∧
        p.1.start.val ≤ p.1.end.val ∧
        (p.2 = true ↔ ∀ j, j < p.1.start.val → a.val[j]? = b.val[j]?))
      (fun y => y = decide (a.val = b.val))
    · rintro ⟨it', res'⟩ hp
      obtain ⟨hp1, hp2, hp3⟩ := hp
      obtain ⟨v, hv, hP⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp
        (hbody it' res' hp1 hlen hp2 hp3)
      show Aeneas.Std.WP.spec (alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq_loop.body inst a b it' res') _
      rw [hv, Aeneas.Std.WP.spec_ok]
      cases v with
      | done y => exact hP
      | cont q => exact hP
    · exact ⟨hend, hle, hres⟩
  unfold alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq
  mvcgen
  · rename_i r1 h1 r2 h2
    intro h3
    subst h1 h2
    have hl : a.val.length = b.val.length := by scalar_tac
    exact hloop { start := 0#usize, «end» := Slice.len a } true (by simp [Slice.len]) hl
      (by simp [Slice.len]) (by simp) trivial
  · rename_i r1 h1 r2 hne h2
    subst h1 h2
    symm
    simp only [decide_eq_false_iff_not]
    intro hab
    exact hne (UScalar.eq_of_val_eq (by simp [Slice.len, hab]))

/-- `Vec<u8>::eq`: `decide` of list equality. -/
@[spec] theorem alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq_U8_spec (a b : alloc.vec.Vec Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq core.U8.Insts.CoreCmpPartialEqU8 a b
    ⦃ ⇓ r => ⌜ r = decide (a.val = b.val) ⌝ ⦄ :=
  alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq_spec _ a b
    core.U8.Insts.CoreCmpPartialEqU8.eq_decide_spec

/-- `TlsByteVecU8::eq`: `decide` of equality of the contents. -/
@[spec] theorem tls_vec.TlsByteVecU8.Insts.CoreCmpPartialEqTlsByteVecU8.eq_spec
    (a b : tls_vec.TlsByteVecU8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU8.Insts.CoreCmpPartialEqTlsByteVecU8.eq a b
    ⦃ ⇓ r => ⌜ r = decide (a.vec.val = b.vec.val) ⌝ ⦄ := by
  unfold tls_vec.TlsByteVecU8.Insts.CoreCmpPartialEqTlsByteVecU8.eq
  mvcgen

/-- `TlsByteVecU16::serialize_bytes_bytes`, when it returns `Ok`, gives the 2-byte length prefix followed by the payload. -/
theorem tls_vec.TlsByteVecU16.serialize_bytes_bytes_content (self : tls_vec.TlsByteVecU16) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU16.serialize_bytes_bytes self
    ⦃ ⇓? r => ⌜ ∀ out : alloc.vec.Vec Std.U8, r = .Ok out →
        ∃ n : Std.U16, n.val = self.vec.val.length ∧
          out.val = (Aeneas.Std.core.num.U16.to_be_bytes n).val ++ self.vec.val ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU16.serialize_bytes_bytes,
    tls_vec.TlsByteVecU16.get_content_lengths_partial,
    checked_alloc_len_total, alloc.vec.Vec.extend_from_slice_U8_spec,
    core.U16.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from_char,
    alloc.vec.Vec.with_capacity, core.result.Result.unwrap_ok_spec, U16_serialize_char,
    alloc.vec.Vec.len_spec, tls_vec.TlsByteVecU16.as_slice, CoreModels.core.slice.Slice.len_spec,
    tls_vec.TlsByteVecU16.assert_written_bytes_total]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  all_goals (try casesm* (∃ _, _), (_ ∧ _))
  all_goals subst_vars
  all_goals (simp_all [Slice.len, Slice.new])
  all_goals first
    | omega
    | scalar_tac
    | (obtain ⟨y, hy, -⟩ := ‹∃ y, _ = _ ∧ _›; exact ⟨y, hy⟩)
    | exact ⟨_, ‹_›, rfl⟩
    | (intro _ out h; cases h)

/-- `TlsByteVecU16::deserialize_bytes_bytes` never panics; on success the input is the 2-byte length prefix, the payload, then the remainder. -/
theorem tls_vec.TlsByteVecU16.deserialize_content (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU16.deserialize_bytes_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : tls_vec.TlsByteVecU16) (t : Slice Std.U8), r = .Ok (v, t) →
        ∃ n : Std.U16, n.val = v.vec.val.length ∧
          bytes.val = (Aeneas.Std.core.num.U16.to_be_bytes n).val ++ (v.vec.val ++ t.val) ⌝ ⦄ := by
  mvcgen [-core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_some_spec,
    tls_vec.TlsByteVecU16.deserialize_bytes_bytes, U16_deserialize_char,
    core.option.Option.ok_or_spec,
    core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_content_spec]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  · exact ⟨_, ‹_›⟩
  · rename_i r0 hP r1 p x1 r2 htf r3 hr3 o hca r4 hr4 cf1 val x2 o1 hget1 r5 hr5 cf2 val1 x3
      vec hvec o2 hget2 r6 hr6 cf3 val2 x4 e0 e1 e2 e3
    intro v t h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (core.result.Result.Ok.inj h)
    have hl : 2 ≤ bytes.val.length := by
      by_contra hn
      rw [hP.2 (by omega)] at e0
      cases e0
    obtain ⟨a, tt, ha, htt, hr⟩ := hP.1 hl
    rw [hr] at e0
    have hp := core.result.Result.Ok.inj e0
    have hpt : p.2 = tt := by rw [← hp]
    have hpp : p.1 = Aeneas.Std.core.num.U16.from_be_bytes a := by rw [← hp]
    have h1 := hget1 val1 (ok_or_eq_ok hr5 e2)
    have h2 : val.val = r3.val + 2 := by
      by_cases hov : r3.val + (2#usize).val ≤ Usize.max
      · obtain ⟨z, hz1, hz2⟩ := hca.1 hov
        rw [hz1] at hr4
        have := core.result.Result.Ok.inj (hr4.symm.trans e1)
        subst this
        simpa using hz2
      · have := hca.2 (by omega)
        rw [this] at hr4
        rw [hr4] at e1
        cases e1
    have ho2 := ok_or_eq_ok hr6 e3
    have hle : r3.val ≤ p.2.val.length := by
      by_contra hn
      rw [hget2.2 (by omega)] at ho2
      cases ho2
    obtain ⟨t2, ht2, ht2'⟩ := hget2.1 hle
    rw [ht2] at ho2
    have hv2 := Option.some.inj ho2
    subst hv2
    subst hvec
    have hc := core.result.Result.Ok.inj (hr3.symm.trans htf)
    have hone : (2#usize).val = 2 := rfl
    have hb : r3.val = p.1.val := by rw [hc]; simp
    have ha1 : a.val = (Aeneas.Std.core.num.U16.to_be_bytes p.1).val := by
      have := U16_to_be_bytes_from_be_bytes a
      rw [← hpp] at this
      rw [← this]
    have hba : bytes.val = a.val ++ tt.val := by
      rw [ha, htt, List.take_append_drop]
    have hv : vec.val = tt.val.take r3.val := by
      have : val.val - (2#usize).val = r3.val := by omega
      rw [h1.2.2, this, htt, hone]
    have ht : t2.val = tt.val.drop r3.val := by rw [ht2', hpt]
    refine ⟨p.1, ?_, ?_⟩
    · rw [hv]
      have : tt.val.length = bytes.val.length - 2 := by rw [htt]; simp
      simp only [List.length_take]
      omega
    · show bytes.val = (Aeneas.Std.core.num.U16.to_be_bytes p.1).val ++ (vec.val ++ t2.val)
      rw [hba, ha1, hv, ht, List.take_append_drop]
  · intro _ v t h; cases h
  · intro _ v t h; cases h
  · intro _ v t h; cases h
  · intro _ v t h; cases h

/-- `TlsByteVecU32::serialize_bytes_bytes`, when it returns `Ok`, gives the 4-byte length prefix followed by the payload. -/
theorem tls_vec.TlsByteVecU32.serialize_bytes_bytes_content (self : tls_vec.TlsByteVecU32) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU32.serialize_bytes_bytes self
    ⦃ ⇓? r => ⌜ ∀ out : alloc.vec.Vec Std.U8, r = .Ok out →
        ∃ n : Std.U32, n.val = self.vec.val.length ∧
          out.val = (Aeneas.Std.core.num.U32.to_be_bytes n).val ++ self.vec.val ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU32.serialize_bytes_bytes,
    tls_vec.TlsByteVecU32.get_content_lengths_partial,
    checked_alloc_len_total, alloc.vec.Vec.extend_from_slice_U8_spec,
    core.U32.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from_char,
    alloc.vec.Vec.with_capacity, core.result.Result.unwrap_ok_spec, U32_serialize_char,
    alloc.vec.Vec.len_spec, tls_vec.TlsByteVecU32.as_slice, CoreModels.core.slice.Slice.len_spec,
    tls_vec.TlsByteVecU32.assert_written_bytes_total]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  all_goals (try casesm* (∃ _, _), (_ ∧ _))
  all_goals subst_vars
  all_goals (simp_all [Slice.len, Slice.new])
  all_goals first
    | omega
    | scalar_tac
    | (obtain ⟨y, hy, -⟩ := ‹∃ y, _ = _ ∧ _›; exact ⟨y, hy⟩)
    | exact ⟨_, ‹_›, rfl⟩
    | (intro _ out h; cases h)

/-- `TlsByteVecU32::deserialize_bytes_bytes` never panics; on success the input is the 4-byte length prefix, the payload, then the remainder. -/
theorem tls_vec.TlsByteVecU32.deserialize_content (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU32.deserialize_bytes_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : tls_vec.TlsByteVecU32) (t : Slice Std.U8), r = .Ok (v, t) →
        ∃ n : Std.U32, n.val = v.vec.val.length ∧
          bytes.val = (Aeneas.Std.core.num.U32.to_be_bytes n).val ++ (v.vec.val ++ t.val) ⌝ ⦄ := by
  mvcgen [-core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_some_spec,
    tls_vec.TlsByteVecU32.deserialize_bytes_bytes, U32_deserialize_char,
    core.option.Option.ok_or_spec,
    core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_content_spec]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  · exact ⟨_, ‹_›⟩
  · rename_i r0 hP r1 p x1 r2 htf r3 hr3 o hca r4 hr4 cf1 val x2 o1 hget1 r5 hr5 cf2 val1 x3
      vec hvec o2 hget2 r6 hr6 cf3 val2 x4 e0 e1 e2 e3
    intro v t h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (core.result.Result.Ok.inj h)
    have hl : 4 ≤ bytes.val.length := by
      by_contra hn
      rw [hP.2 (by omega)] at e0
      cases e0
    obtain ⟨a, tt, ha, htt, hr⟩ := hP.1 hl
    rw [hr] at e0
    have hp := core.result.Result.Ok.inj e0
    have hpt : p.2 = tt := by rw [← hp]
    have hpp : p.1 = Aeneas.Std.core.num.U32.from_be_bytes a := by rw [← hp]
    have h1 := hget1 val1 (ok_or_eq_ok hr5 e2)
    have h2 : val.val = r3.val + 4 := by
      by_cases hov : r3.val + (4#usize).val ≤ Usize.max
      · obtain ⟨z, hz1, hz2⟩ := hca.1 hov
        rw [hz1] at hr4
        have := core.result.Result.Ok.inj (hr4.symm.trans e1)
        subst this
        simpa using hz2
      · have := hca.2 (by omega)
        rw [this] at hr4
        rw [hr4] at e1
        cases e1
    have ho2 := ok_or_eq_ok hr6 e3
    have hle : r3.val ≤ p.2.val.length := by
      by_contra hn
      rw [hget2.2 (by omega)] at ho2
      cases ho2
    obtain ⟨t2, ht2, ht2'⟩ := hget2.1 hle
    rw [ht2] at ho2
    have hv2 := Option.some.inj ho2
    subst hv2
    subst hvec
    have hc := core.result.Result.Ok.inj (hr3.symm.trans htf)
    have hone : (4#usize).val = 4 := rfl
    have hb : r3.val = p.1.val := by rw [hc]; simp
    have ha1 : a.val = (Aeneas.Std.core.num.U32.to_be_bytes p.1).val := by
      have := U32_to_be_bytes_from_be_bytes a
      rw [← hpp] at this
      rw [← this]
    have hba : bytes.val = a.val ++ tt.val := by
      rw [ha, htt, List.take_append_drop]
    have hv : vec.val = tt.val.take r3.val := by
      have : val.val - (4#usize).val = r3.val := by omega
      rw [h1.2.2, this, htt, hone]
    have ht : t2.val = tt.val.drop r3.val := by rw [ht2', hpt]
    refine ⟨p.1, ?_, ?_⟩
    · rw [hv]
      have : tt.val.length = bytes.val.length - 4 := by rw [htt]; simp
      simp only [List.length_take]
      omega
    · show bytes.val = (Aeneas.Std.core.num.U32.to_be_bytes p.1).val ++ (vec.val ++ t2.val)
      rw [hba, ha1, hv, ht, List.take_append_drop]
  · intro _ v t h; cases h
  · intro _ v t h; cases h
  · intro _ v t h; cases h
  · intro _ v t h; cases h


/-- `TlsByteVecU16::eq`: `decide` of equality of the contents. -/
@[spec] theorem tls_vec.TlsByteVecU16.Insts.CoreCmpPartialEqTlsByteVecU16.eq_spec
    (a b : tls_vec.TlsByteVecU16) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU16.Insts.CoreCmpPartialEqTlsByteVecU16.eq a b
    ⦃ ⇓ r => ⌜ r = decide (a.vec.val = b.vec.val) ⌝ ⦄ := by
  unfold tls_vec.TlsByteVecU16.Insts.CoreCmpPartialEqTlsByteVecU16.eq
  mvcgen

/-- `TlsByteVecU24::eq`: `decide` of equality of the contents. -/
@[spec] theorem tls_vec.TlsByteVecU24.Insts.CoreCmpPartialEqTlsByteVecU24.eq_spec
    (a b : tls_vec.TlsByteVecU24) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU24.Insts.CoreCmpPartialEqTlsByteVecU24.eq a b
    ⦃ ⇓ r => ⌜ r = decide (a.vec.val = b.vec.val) ⌝ ⦄ := by
  unfold tls_vec.TlsByteVecU24.Insts.CoreCmpPartialEqTlsByteVecU24.eq
  mvcgen

/-- `TlsByteVecU32::eq`: `decide` of equality of the contents. -/
@[spec] theorem tls_vec.TlsByteVecU32.Insts.CoreCmpPartialEqTlsByteVecU32.eq_spec
    (a b : tls_vec.TlsByteVecU32) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU32.Insts.CoreCmpPartialEqTlsByteVecU32.eq a b
    ⦃ ⇓ r => ⌜ r = decide (a.vec.val = b.vec.val) ⌝ ⦄ := by
  unfold tls_vec.TlsByteVecU32.Insts.CoreCmpPartialEqTlsByteVecU32.eq
  mvcgen

/-- `usize::from(U24)`, when it returns: the big-endian value of the three bytes (it panics on 32-bit `usize`). -/
theorem Usize.Insts.CoreConvertFromU24.from_content (value : U24) :
    ⦃ ⌜ True ⌝ ⦄ Usize.Insts.CoreConvertFromU24.from value
    ⦃ ⇓? r => ⌜ ∀ b0 b1 b2 : Std.U8, value.val = [b0, b1, b2] →
        r.val = b0.val * 65536 + b1.val * 256 + b2.val ⌝ ⦄ := by
  mvcgen [Usize.Insts.CoreConvertFromU24.from, FromUsizeU24.from.LEN,
    core.mem.size_of_Usize_spec, core.Array.Insts.CoreOpsIndexIndexMut.index_mut,
    core.array.Array.as_mut_slice, rust_primitives.slice.array_as_mut_slice,
    core.slice.Slice.copy_from_slice_U8_spec, core.num.Usize.from_be_bytes,
    rust_primitives.arithmetic.from_be_bytes_usize]
  · rename_i bytes0 n hn i1 hi1 hle
    have hnb := System.Platform.numBits_eq
    have : (Std.Array.to_slice_mut bytes0).1.length = 8 := by
      simp [Std.Array.to_slice_mut, Std.Array.to_slice, bytes0]
    scalar_tac
  · rename_i bytes0 n hn i1 hi1 hle p back hp s2 bytes1 hc
    have hnb := System.Platform.numBits_eq
    obtain ⟨hp1, hp2⟩ := hp
    obtain ⟨hlen, hs2⟩ := hc
    obtain ⟨vl, hvl⟩ := value
    obtain ⟨b0, b1, b2, rfl⟩ := List.length_eq_three.mp (by simpa using hvl)
    have hb0 : bytes0.val = List.replicate 8 0#u8 := rfl
    have hl1 : p.1.val.length = 8 - i1.val := by
      rw [hp1]; simp [Std.Array.to_slice_mut, Std.Array.to_slice, hb0]
    have hl2 : (Std.Array.to_slice (⟨[b0, b1, b2], hvl⟩ : U24)).val.length = 3 := by
      simp [Std.Array.to_slice]
    have hi5 : i1.val = 5 := by
      rw [hl1, hl2] at hlen
      omega
    have hn8 : n.val = 8 := by scalar_tac
    have hnb64 : System.Platform.numBits = 64 := by omega
    have hbytes1 : bytes1.val = [0#u8, 0#u8, 0#u8, 0#u8, 0#u8, b0, b1, b2] := by
      have e2 : (Std.Array.to_slice_mut bytes0).1.val = bytes0.val := rfl
      have e3 : (p.2 s2).val.length = 8 := by
        rw [hp2 s2, List.length_setSlice!, e2, hb0]; simp
      have e1 : bytes1.val = (p.2 s2).val :=
        Std.Array.from_slice_val bytes0 (p.2 s2) (by rw [e3]; rfl)
      rw [e1, hp2 s2, hs2, hi5, e2, hb0]
      simp [Std.Array.to_slice]
      rfl
    rw [hbytes1]
    intro c0 c1 c2 hc012
    have hv := usize_from_zero5_val b0 b1 b2 hnb64
    have h3 : [b0, b1, b2] = [c0, c1, c2] := hc012
    simp only [List.cons.injEq, and_true] at h3
    obtain ⟨rfl, rfl, rfl⟩ := h3
    exact hv

/-- A list of length 8 is a literal list. -/
theorem list_eq_eight {α : Type} (l : List α) (h : l.length = 8) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7, l = [a0, a1, a2, a3, a4, a5, a6, a7] := by
  match l, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7], _ => exact ⟨_, _, _, _, _, _, _, _, rfl⟩

/-- Value of eight big-endian bytes. -/
theorem fromBEBytes_eight_toNat (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (BitVec.fromBEBytes [b0, b1, b2, b3, b4, b5, b6, b7]).toNat =
      b0.toNat * 72057594037927936 + b1.toNat * 281474976710656 + b2.toNat * 1099511627776 +
      b3.toNat * 4294967296 + b4.toNat * 16777216 + b5.toNat * 65536 + b6.toNat * 256 +
      b7.toNat := by
  unfold BitVec.fromBEBytes
  rw [BitVec.toNat_cast, fromLEBytes_toNat]
  simp [List.foldr]
  omega

/-- Arithmetic of the eight big-endian bytes of a value below `2^24`. -/
theorem eight_bytes_low3 (x0 x1 x2 x3 x4 x5 x6 x7 v : Nat)
    (h0 : x0 < 2 ^ 8) (h1 : x1 < 2 ^ 8) (h2 : x2 < 2 ^ 8) (h3 : x3 < 2 ^ 8) (h4 : x4 < 2 ^ 8)
    (h5 : x5 < 2 ^ 8) (h6 : x6 < 2 ^ 8) (h7 : x7 < 2 ^ 8) (hv : v ≤ 16777215)
    (h : v = x0 * 72057594037927936 + x1 * 281474976710656 + x2 * 1099511627776 +
      x3 * 4294967296 + x4 * 16777216 + x5 * 65536 + x6 * 256 + x7) :
    v = x5 * 65536 + x6 * 256 + x7 := by
  simp only [Nat.reducePow] at h0 h1 h2 h3 h4 h5 h6 h7
  subst h
  have e0 : x0 = 0 := by omega
  subst e0
  have e1 : x1 = 0 := by omega
  subst e1
  have e2 : x2 = 0 := by omega
  subst e2
  have e3 : x3 = 0 := by omega
  subst e3
  have e4 : x4 = 0 := by omega
  subst e4
  omega

/-- `U24::try_from(usize)`, when it returns `Ok a`: `a` holds the three low bytes of the value, which fits. -/
theorem U24.Insts.CoreConvertTryFromUsizeError.try_from_content (value : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ U24.Insts.CoreConvertTryFromUsizeError.try_from value
    ⦃ ⇓? r => ⌜ ∀ a : U24, r = .Ok a → ∃ b0 b1 b2 : Std.U8, a.val = [b0, b1, b2] ∧
        value.val = b0.val * 65536 + b1.val * 256 + b2.val ⌝ ⦄ := by
  mvcgen [U24.Insts.CoreConvertTryFromUsizeError.try_from, TryFromU24UsizeError.try_from.LEN,
    core.mem.size_of_Usize_spec, core.num.Usize.to_be_bytes,
    rust_primitives.arithmetic.to_be_bytes_usize]
  · intro a h; cases h
  · rename_i r3 ha1 ha2 ha3 r2 hv hlt hmax n hn i3 hi3 hle o
    intro h1 h2
    have hnb := System.Platform.numBits_eq
    have hl8 : (Std.Array.to_slice (⟨List.map UScalar.mk (BitVec.setWidth 64 value.bv).toBEBytes,
        by grind [BitVec.toBEBytes_length]⟩ : Std.Array Std.U8 8#usize)).val.length = 8 := by
      simp [Std.Array.to_slice]
    obtain ⟨t, ht, htv⟩ := h1 (by rw [hl8]; scalar_tac)
    refine ⟨t, ht, ?_⟩
    simp only [PostCond.ok]
    mvcgen [core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from_spec]
    · rename_i r1 hr1 cf val x hcf
      intro a hA
      obtain rfl := core.result.Result.Ok.inj hA
      have hr1ok := continue_eq_tryCF.mp hcf
      have ht3 : t.val.length = 3 := by
        by_contra hne
        rw [hr1.2 hne] at hr1ok
        cases hr1ok
      have e3 : (3#usize).val = 3 := rfl
      have e1 : (1#usize).val = 1 := rfl
      have hnb64 : System.Platform.numBits = 64 := by
        rcases hnb with h | h
        · exfalso
          have hn4 : n.val = 4 := by omega
          have hi31 : i3.val = 1 := by omega
          have : t.val.length = 7 := by
            rw [htv]; simp [Std.Array.to_slice, hi31]
          omega
        · exact h
      have hi35 : i3.val = 5 := by
        have : n.val = 8 := by omega
        omega
      have hsz : Usize.size = 2 ^ 64 := by
        simp [Usize.size, Usize.numBits, UScalarTy.numBits, hnb64]
      have hr3v : r3.val = 16777216 := by
        rw [ha1, e1, hsz]
        have : (24#i32).toNat = 24 := rfl
        rw [this, Nat.shiftLeft_eq]; norm_num
      have hval : value.val ≤ 16777215 := by
        have : ¬ value.val > r2.val := hmax
        omega
      have hvlt : value.val < 2 ^ 64 := by
        show value.bv.toNat < 2 ^ 64
        exact Nat.lt_of_lt_of_le value.bv.isLt (by rw [hnb64])
      -- the eight big-endian bytes
      obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, hbl⟩ :=
        list_eq_eight (BitVec.setWidth 64 value.bv).toBEBytes (by simpa using BitVec.toBEBytes_length (BitVec.setWidth 64 value.bv))
      have hnat : value.val = (BitVec.fromBEBytes [c0, c1, c2, c3, c4, c5, c6, c7]).toNat := by
        have h := fromBEBytes_toBEBytes_toNat (w := 64) (by norm_num) (BitVec.setWidth 64 value.bv)
        rw [hbl, BitVec.toNat_setWidth] at h
        rw [h]
        exact (Nat.mod_eq_of_lt hvlt).symm
      rw [fromBEBytes_eight_toNat] at hnat
      have hc0 := c0.isLt
      have hc1 := c1.isLt
      have hc2 := c2.isLt
      have hc3 := c3.isLt
      have hc4 := c4.isLt
      have hc5 := c5.isLt
      have hc6 := c6.isLt
      have hc7 := c7.isLt
      have hvt : val.val = t.val := ((hr1.1 ht3).elim fun a ha => by
        rw [hr1ok] at ha
        rw [(core.result.Result.Ok.inj ha.1)]
        exact ha.2)
      simp only [Std.Array.to_slice, hbl, hi35, List.map_cons, List.map_nil] at htv
      exact ⟨UScalar.mk c5, UScalar.mk c6, UScalar.mk c7, by rw [hvt, htv]; rfl, by
        show value.val = c5.toNat * 65536 + c6.toNat * 256 + c7.toNat
        exact eight_bytes_low3 _ _ _ _ _ _ _ _ _ hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hval hnat⟩
    · try_vcs [Error.Insts.CoreConvertFromTryFromSliceError.from]
      intro a h; cases h

/-- `TlsByteVecU24::serialize_bytes_bytes`, when it returns `Ok`, gives the 3-byte length prefix followed by the payload (partial: `usize::from(U24)` may panic on 32-bit `usize`). -/
theorem tls_vec.TlsByteVecU24.serialize_bytes_bytes_content (self : tls_vec.TlsByteVecU24) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU24.serialize_bytes_bytes self
    ⦃ ⇓? r => ⌜ ∀ out : alloc.vec.Vec Std.U8, r = .Ok out →
        ∃ b0 b1 b2 : Std.U8, b0.val * 65536 + b1.val * 256 + b2.val = self.vec.val.length ∧
          out.val = b0 :: b1 :: b2 :: self.vec.val ⌝ ⦄ := by
  mvcgen [-core.result.Result.unwrap_ok_spec, tls_vec.TlsByteVecU24.serialize_bytes_bytes,
    tls_vec.TlsByteVecU24.get_content_lengths_partial,
    checked_alloc_len_total, alloc.vec.Vec.extend_from_slice_U8_spec,
    U24.Insts.CoreConvertTryFromUsizeError.try_from_content,
    alloc.vec.Vec.with_capacity, core.result.Result.unwrap_partial, U24_serialize_char,
    alloc.vec.Vec.len_spec, tls_vec.TlsByteVecU24.as_slice, CoreModels.core.slice.Slice.len_spec,
    tls_vec.TlsByteVecU24.assert_written_bytes_total]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  all_goals (try casesm* (∃ _, _), (_ ∧ _))
  all_goals subst_vars
  all_goals (simp_all [Slice.len, Slice.new])
  all_goals first
    | omega
    | scalar_tac
    | (obtain ⟨b0, b1, b2, h3, h4⟩ := ‹∃ b0 b1 b2, _ ∧ _›; exact ⟨b0, b1, b2, h4.symm, by rw [h3]; rfl⟩)
    | (intro _ out h; cases h)

/-- `usize::try_from(U24)` through the blanket `TryFrom` impl for `Into`: when it returns, it is
`Ok` of the big-endian value of the three bytes. -/
theorem core.convert.TryFromTUInfallible.Blanket.try_from_Usize_U24_content (x : U24) :
    ⦃ ⌜ True ⌝ ⦄
    core.convert.TryFromTUInfallible.Blanket.try_from
      (core.convert.Into.Blanket Usize.Insts.CoreConvertFromU24) x
    ⦃ ⇓? r => ⌜ ∃ y, r = .Ok y ∧ ∀ b0 b1 b2 : Std.U8, x.val = [b0, b1, b2] →
        y.val = b0.val * 65536 + b1.val * 256 + b2.val ⌝ ⦄ := by
  unfold core.convert.TryFromTUInfallible.Blanket.try_from core.convert.Into.Blanket
  mvcgen [core.convert.Into.Blanket.into, Usize.Insts.CoreConvertFromU24.from_content]
  exact ⟨_, rfl, ‹_›⟩

/-- `TlsByteVecU24::deserialize_bytes_bytes` (partial: `usize::from(U24)` may panic on 32-bit `usize`); on success the input is the 3-byte length prefix, the payload, then the remainder. -/
theorem tls_vec.TlsByteVecU24.deserialize_content (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU24.deserialize_bytes_bytes bytes
    ⦃ ⇓? r => ⌜ ∀ (v : tls_vec.TlsByteVecU24) (t : Slice Std.U8), r = .Ok (v, t) →
        ∃ b0 b1 b2 : Std.U8, b0.val * 65536 + b1.val * 256 + b2.val = v.vec.val.length ∧
          bytes.val = b0 :: b1 :: b2 :: (v.vec.val ++ t.val) ⌝ ⦄ := by
  mvcgen [-core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_some_spec,
    tls_vec.TlsByteVecU24.deserialize_bytes_bytes, U24_deserialize_char,
    core.convert.TryFromTUInfallible.Blanket.try_from_Usize_U24_content,
    core.option.Option.ok_or_spec,
    core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_content_spec]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  · obtain ⟨y, hy, -⟩ := ‹∃ y, _ = _ ∧ _›
    exact ⟨y, hy⟩
  · rename_i r0 hP r1 p x1 r2 htf r3 hr3 o hca r4 hr4 cf1 val x2 o1 hget1 r5 hr5 cf2 val1 x3
      vec hvec o2 hget2 r6 hr6 cf3 val2 x4 e0 e1 e2 e3
    intro v t h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (core.result.Result.Ok.inj h)
    have hl : 3 ≤ bytes.val.length := by
      by_contra hn
      rw [hP.2 (by omega)] at e0
      cases e0
    obtain ⟨a, tt, ha, htt, hr⟩ := hP.1 hl
    rw [hr] at e0
    have hp := core.result.Result.Ok.inj e0
    have hpt : p.2 = tt := by rw [← hp]
    have hpp : p.1 = a := by rw [← hp]
    have h1 := hget1 val1 (ok_or_eq_ok hr5 e2)
    have h2 : val.val = r3.val + 3 := by
      by_cases hov : r3.val + (3#usize).val ≤ Usize.max
      · obtain ⟨z, hz1, hz2⟩ := hca.1 hov
        rw [hz1] at hr4
        have := core.result.Result.Ok.inj (hr4.symm.trans e1)
        subst this
        simpa using hz2
      · have := hca.2 (by omega)
        rw [this] at hr4
        rw [hr4] at e1
        cases e1
    have ho2 := ok_or_eq_ok hr6 e3
    have hle : r3.val ≤ p.2.val.length := by
      by_contra hn
      rw [hget2.2 (by omega)] at ho2
      cases ho2
    obtain ⟨t2, ht2, ht2'⟩ := hget2.1 hle
    rw [ht2] at ho2
    have hv2 := Option.some.inj ho2
    subst hv2
    subst hvec
    obtain ⟨y, hy, hyv⟩ := htf
    have hc := core.result.Result.Ok.inj (hr3.symm.trans hy)
    have hone : (3#usize).val = 3 := rfl
    have hal : a.val.length = 3 := a.property
    obtain ⟨b0, b1, b2, hab⟩ := List.length_eq_three.mp hal
    have hb : r3.val = b0.val * 65536 + b1.val * 256 + b2.val := by
      rw [hc]; exact hyv b0 b1 b2 (by rw [hpp]; exact hab)
    have hba : bytes.val = a.val ++ tt.val := by
      rw [ha, htt, List.take_append_drop]
    have hv : vec.val = tt.val.take r3.val := by
      have : val.val - (3#usize).val = r3.val := by omega
      rw [h1.2.2, this, htt, hone]
    have ht : t2.val = tt.val.drop r3.val := by rw [ht2', hpt]
    refine ⟨b0, b1, b2, ?_, ?_⟩
    · rw [hv]
      have : tt.val.length = bytes.val.length - 3 := by rw [htt]; simp
      simp only [List.length_take]
      omega
    · show bytes.val = b0 :: b1 :: b2 :: (vec.val ++ t2.val)
      rw [hba, hab, hv, ht, List.take_append_drop]
      rfl
  · intro _ v t h; cases h
  · intro _ v t h; cases h
  · intro _ v t h; cases h
  · intro _ v t h; cases h

/-! ### Specs of the hand-translated `<&[T]>::tls_serialize_bytes` -/

/-- One step of the serialisation loop (no element fails): either the iterator is exhausted, or
the head `e` is consumed and `f e` is appended. -/
def loop_append_step {T : Type} (f : T → List Std.U8) (it' : core.slice.iter.Iter T)
    (o : alloc.vec.Vec Std.U8)
    (r : ControlFlow (core.slice.iter.Iter T × alloc.vec.Vec Std.U8)
      (alloc.vec.Vec Std.U8 × core.option.Option Error)) : Prop :=
  match r with
  | .done y => y.1 = o ∧ y.2 = core.option.Option.None ∧ (it' : Slice T).val = []
  | .cont p => ∃ e, (it' : Slice T).val = e :: (p.1 : Slice T).val ∧ p.2.val = o.val ++ f e

/-- A `loop` that walks a slice iterator and appends `f e` to the output per element (the
serialisation loop of the hand-translated slice serializer, when no element fails).
`hbody`: one step. -/
theorem loop_append_spec {T : Type} (f : T → List Std.U8) (it : core.slice.iter.Iter T)
    (out : alloc.vec.Vec Std.U8)
    (body : core.slice.iter.Iter T × alloc.vec.Vec Std.U8 →
      RustM (ControlFlow (core.slice.iter.Iter T × alloc.vec.Vec Std.U8)
        (alloc.vec.Vec Std.U8 × core.option.Option Error)))
    (h : out.val.length + ((it : Slice T).val.flatMap f).length ≤ Std.Usize.max)
    (hbody : ∀ (it' : core.slice.iter.Iter T) (o : alloc.vec.Vec Std.U8),
      o.val.length + ((it' : Slice T).val.flatMap f).length ≤ Std.Usize.max →
      ⦃ ⌜ True ⌝ ⦄ body (it', o)
      ⦃ ⇓ r => ⌜ loop_append_step f it' o r ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄ loop body (it, out)
    ⦃ ⇓ r => ⌜ r.2 = core.option.Option.None ∧
        r.1.val = out.val ++ (it : Slice T).val.flatMap f ⌝ ⦄ := by
  apply Aeneas.Std.WP.spec_to_mvcgen
  apply Aeneas.Std.loop.spec_decr_nat
    (fun p : core.slice.iter.Iter T × alloc.vec.Vec Std.U8 => (p.1 : Slice T).val.length)
    (fun p => p.2.val ++ (p.1 : Slice T).val.flatMap f = out.val ++ (it : Slice T).val.flatMap f)
  · rintro ⟨it', a⟩ hinv
    have hb := Aeneas.Std.WP.exists_imp_spec
      (Aeneas.Std.WP.triple_iff_exists_ok.mp (hbody it' a (by
        simp only at hinv
        have := congrArg List.length hinv
        simp only [List.length_append] at this
        omega)))
    apply Aeneas.Std.WP.spec_mono hb
    intro r hr
    simp only at hinv
    cases r with
    | done y =>
      obtain ⟨h1, h2, h3⟩ := hr
      refine ⟨h2, ?_⟩
      rw [h1, ← hinv, h3]; simp
    | cont p =>
      obtain ⟨e, hl, hv⟩ := hr
      refine ⟨?_, by simp only [hl]; simp⟩
      simp only [hv, ← hinv, hl, List.flatMap_cons, List.append_assoc]
  · simp

/-- `loop_append_spec` for `u8` elements (each serialises to its big-endian bytes). -/
theorem loop_append_U8_spec (it : core.slice.iter.Iter Std.U8) (out : alloc.vec.Vec Std.U8)
    (body : core.slice.iter.Iter Std.U8 × alloc.vec.Vec Std.U8 →
      RustM (ControlFlow (core.slice.iter.Iter Std.U8 × alloc.vec.Vec Std.U8)
        (alloc.vec.Vec Std.U8 × core.option.Option Error)))
    (h : out.val.length + ((it : Slice Std.U8).val.flatMap
      (fun x => (Aeneas.Std.core.num.U8.to_be_bytes x).val)).length ≤ Std.Usize.max)
    (hbody : ∀ (it' : core.slice.iter.Iter Std.U8) (o : alloc.vec.Vec Std.U8),
      o.val.length + ((it' : Slice Std.U8).val.flatMap
        (fun x => (Aeneas.Std.core.num.U8.to_be_bytes x).val)).length ≤ Std.Usize.max →
      ⦃ ⌜ True ⌝ ⦄ body (it', o)
      ⦃ ⇓ r => ⌜ loop_append_step (fun x => (Aeneas.Std.core.num.U8.to_be_bytes x).val) it' o r ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄ loop body (it, out)
    ⦃ ⇓ r => ⌜ r.2 = core.option.Option.None ∧
        r.1.val = out.val ++ (it : Slice Std.U8).val.flatMap
          (fun x => (Aeneas.Std.core.num.U8.to_be_bytes x).val) ⌝ ⦄ :=
  loop_append_spec (fun x => (Aeneas.Std.core.num.U8.to_be_bytes x).val) it out body h hbody

/-- Concatenating the serialisations of `u8`s gives the list itself. -/
theorem U8_flatMap_to_be_bytes (l : List Std.U8) :
    l.flatMap (fun x => (Aeneas.Std.core.num.U8.to_be_bytes x).val) = l := by
  simp only [U8_to_be_bytes_val]; induction l <;> simp_all

-- `loop_append_U8_spec` needs priority over `mvcgen`'s built-in loop spec.
attribute [local spec high] loop_append_U8_spec in
/-- `<&[u8]>::tls_serialize_bytes` never panics: a slice of at most `2^30 - 1` bytes gives the
varint length prefix followed by the payload (only the length is tracked), a longer one an error. -/
theorem Shared0Slice.serialize_U8_char (s : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ Shared0Slice.Insts.Tls_codecSerializeBytes.tls_serialize_bytes
      U8.Insts.Tls_codecSerializeBytes s
    ⦃ ⇓ r => ⌜ (s.val.length ≤ 2 ^ 30 - 1 → ∃ out : alloc.vec.Vec Std.U8, r = .Ok out ∧
                  out.val.length = s.val.length + varint.lenOf s.val.length) ∧
               (2 ^ 30 - 1 < s.val.length → ∃ e, r = .Err e) ⌝ ⦄ := by
  unfold Shared0Slice.Insts.Tls_codecSerializeBytes.tls_serialize_bytes
  nth_rewrite 1 [slice_iter_ok]
  erw [bind_tc_ok]
  refine triple_bind_of_total (loop_len_sum_spec 1#usize _ 0#usize _ ?hlen ?hbody) ?hk
  case hlen => scalar_tac
  case hbody =>
    intro it a ha
    mvcgen [core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
      U8.Insts.Tls_codecSize.tls_serialized_len, Copied.checked_len_add]
    all_goals (simp_all [tryCF, -List.length_eq_zero_iff]; try scalar_tac)
  case hk =>
    rintro r ⟨v, rfl, hv⟩
    simp only [Copied.varint.TlsVarInt.bytes_len_eq, Copied.varint.TlsVarInt.write_bytes_eq,
      Copied.checked_alloc_len_eq, Copied.quic_vec.ContentLength.from_usize_eq]
    mvcgen [quic_vec.ContentLength.from_usize_spec, varint.TlsVarInt.bytes_len_spec,
      checked_alloc_len_small, alloc.vec.Vec.with_capacity,
      alloc.vec.Vec.resize_U8_len_spec,
      alloc.vec.Vec.Insts.CoreOpsDerefDerefMutSlice.deref_mut, alloc.vec.Vec.as_mut_slice,
      rust_primitives.sequence.seq_to_slice_mut, varint.TlsVarInt.write_bytes_spec,
      core.slice.Slice.iter, core.iter.traits.collect.IntoIterator.Blanket.into_iter, loop_append_U8_spec,
      core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next, U8_serialize_char,
      alloc.vec.Vec.append, rust_primitives.sequence.seq_concat]
    all_goals (try simp only [continue_eq_tryCF] at *)
    all_goals subst_vars
    all_goals (try simp only [Slice.len_val] at *)
    · omega
    · -- the output (prefix + payload) fits in `usize`
      rename_i _ val len hbl _ out hout back w hw _ hOk _ hval _
      have hc := varint.lenOf_char _ _ hbl
      have hl := (hw.2 (by omega)).2
      have ho := core.result.Result.Ok.inj hOk
      show w.2.val.length + _ ≤ _
      rw [U8_flatMap_to_be_bytes]
      scalar_tac
    · -- iterator exhausted
      rename_i it o hb hlen _ _ _ _
      refine ⟨rfl, rfl, ?_⟩
      have : (it : Slice U8).val.length = 0 := by scalar_tac
      exact List.length_eq_zero_iff.mp this
    · -- one more element
      rename_i it o hb hne hlt bytes hv combined hcl _ _ _ _
      obtain ⟨b, hbb, hbv⟩ := hv
      obtain rfl := core.result.Result.Ok.inj hbb
      refine ⟨(it : Slice U8).val[0], ?_, ?_⟩
      · simp [List.getElem_zero, List.cons_head_tail]
      · simp [combined, hbv, List.get_eq_getElem]; rfl
    · -- the vector would exceed `usize`: impossible (bound)
      rename_i it o hb hne hlt bytes hv combined hncl _ _ _ _
      obtain ⟨b, hbb, hbv⟩ := hv
      obtain rfl := core.result.Result.Ok.inj hbb
      exfalso; apply hncl
      have h1 : (bytes : Slice U8).val.length = 1 := by rw [hbv, U8_to_be_bytes_val]; rfl
      rw [U8_flatMap_to_be_bytes] at hb
      simp only [combined, List.length_append]
      scalar_tac
    · -- the serialisation of a `u8` is not an error
      rename_i it o hb hne hlt err hv _ _ _ _
      obtain ⟨_, h, _⟩ := hv
      cases h
    · -- the iterator has an element
      rename_i it o hb hne hnlt _ _ _ _
      exfalso; apply hne
      apply UScalar.eq_of_val_eq
      simp only [Slice.len_val]
      scalar_tac
    · -- no failure
      rename_i r err hs hr _ _ _ _
      simp [hr.1] at hs
    · -- the length check passes
      rename_i val lenlen hbl _ out hout back w hw _ r hx hr i hne hOk hr1 hval hn hi hle
      exfalso
      have hc := varint.lenOf_char _ _ hbl
      have hl := (hw.2 (by omega)).2
      have ho := core.result.Result.Ok.inj hOk
      have h3 : Slice.length r.1 = w.2.val.length + Slice.length s := by
        simp only [Slice.length, hr.2, List.length_append, U8_flatMap_to_be_bytes]; rfl
      simp only [bne_iff_ne, ne_eq] at hne
      exact hne (by scalar_tac)
    · -- success
      rename_i val lenlen hbl _ out hout back w hw _ r hx hr i hne hOk hr1 hval hn hi hle
      have hc := varint.lenOf_char _ _ hbl
      have hl := (hw.2 (by omega)).2
      have ho := core.result.Result.Ok.inj hOk
      have h3 : Slice.length r.1 = w.2.val.length + Slice.length s := by
        simp only [Slice.length, hr.2, List.length_append, U8_flatMap_to_be_bytes]; rfl
      have hv' : val.val = s.val.length := by scalar_tac
      rw [hv'] at hc
      have hs : s.val.length ≤ 2 ^ 30 - 1 := by omega
      refine ⟨fun _ => ⟨_, rfl, ?_⟩, fun h => absurd h (by omega)⟩
      have h4 : (r.1 : Slice U8).val.length = w.2.val.length + s.val.length := h3
      omega
    · -- `usize` subtraction does not underflow
      rename_i val lenlen hbl _ out hout back w hw _ r hx hr hOk hr1 hval hn hlt
      exfalso
      have hc := varint.lenOf_char _ _ hbl
      have hl := (hw.2 (by omega)).2
      have h3 : Slice.length r.1 = w.2.val.length + Slice.length s := by
        simp only [Slice.length, hr.2, List.length_append, U8_flatMap_to_be_bytes]; rfl
      scalar_tac
    · -- `write_bytes` succeeds
      rename_i val lenlen hbl _ out hout back w hw resid hOk hval hn
      have hc := varint.lenOf_char _ _ hbl
      obtain ⟨⟨l, hl, _⟩, _⟩ := hw.2 (by omega)
      intro hb
      rw [hl] at hb
      simp only [tryCF, reduceCtorEq] at hb
    · -- `checked_alloc_len` succeeds
      rename_i val lenlen hbl r hn resid hOk hval
      obtain ⟨n, rfl, _⟩ := hn
      intro hb
      simp only [tryCF, reduceCtorEq] at hb
    · -- `from_usize` fails: the payload is too long
      rename_i acc r hr resid hOk
      apply try_break_vc
      intro e he
      subst he
      have ho := core.result.Result.Ok.inj hOk
      have hr' : 2 ^ 30 - 1 < s.val.length := by simp only at hr; scalar_tac
      mvcgen
      intro _
      exact ⟨fun h => absurd h (by omega), fun _ => ⟨_, rfl⟩⟩
    · intro hb
      simp only [tryCF, reduceCtorEq] at hb

end tls_codec
