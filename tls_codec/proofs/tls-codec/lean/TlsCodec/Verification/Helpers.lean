/- Shared helpers for the proofs in `PanicFreedom.lean` / `FunctionalCorrectness.lean`. -/
import Aeneas
import CoreModels
import Hax
import TlsCodec.Extraction
import TlsCodec.Assumptions.MissingCoreModelsSpecs
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option mvcgen.warning false
set_option hax_mvcgen.warnings false

namespace tls_codec

/-! ### Length sums (`len_add` / `checked_len_add`, opaque)

Both are opaque since the trait-level-spec port (phase 2); `Assumptions/CrateAssumptions.lean`
states their ASSUMED bounds `len_add_spec` / `checked_len_add_spec`. Here their results get
names (`lenAddVal a b`, `checkedLenAddVal a b`, by choice), with equations
(`len_add_ok`, `checked_len_add_ok`) and `@[spec]` triples whose post pins the result, so
`mvcgen` substitutes it; the value is the exact sum whenever it fits (`lenAddVal_val`,
`checkedLenAddVal_val`, conditional, so use them explicitly). Any proof using them shows
the ASSUMED axiom in `#print axioms`. -/

/-- The result of `len_add a b` (ASSUMED to exist, `len_add_spec`). -/
noncomputable def lenAddVal (a b : Std.Usize) : Std.Usize := Classical.choose (len_add_spec a b)

/-- The `Ok` payload of `checked_len_add a b` when the sum fits (ASSUMED to exist,
    `checked_len_add_spec`); `0` otherwise (then the result is `Err`). -/
noncomputable def checkedLenAddVal (a b : Std.Usize) : Std.Usize :=
  if h : a.val + b.val ≤ Usize.max then Classical.choose ((checked_len_add_spec a b).1 h)
  else 0#usize

/-- The result of `checked_len_add a b`: `Ok` of the sum when it fits, else
    `Err InvalidVectorLength` (`checked_len_add_spec`). -/
noncomputable def checkedLenAddRes (a b : Std.Usize) : core.result.Result Std.Usize Error :=
  if a.val + b.val ≤ Usize.max then .Ok (checkedLenAddVal a b) else .Err .InvalidVectorLength

theorem len_add_ok (a b : Std.Usize) : len_add a b = ok (lenAddVal a b) :=
  (Classical.choose_spec (len_add_spec a b)).1

theorem checked_len_add_ok (a b : Std.Usize) :
    checked_len_add a b = ok (checkedLenAddRes a b) := by
  unfold checkedLenAddRes checkedLenAddVal
  by_cases h : a.val + b.val ≤ Usize.max
  · simp only [h, dite_cond_eq_true, if_true]
    exact (Classical.choose_spec ((checked_len_add_spec a b).1 h)).1
  · simp only [h, if_false]
    exact (checked_len_add_spec a b).2 (by omega)

theorem lenAddVal_val (a b : Std.Usize) (h : a.val + b.val ≤ Usize.max) :
    (lenAddVal a b).val = a.val + b.val :=
  (Classical.choose_spec (len_add_spec a b)).2 h

theorem checkedLenAddVal_val (a b : Std.Usize) (h : a.val + b.val ≤ Usize.max) :
    (checkedLenAddVal a b).val = a.val + b.val := by
  unfold checkedLenAddVal
  simp only [h, dite_cond_eq_true]
  exact (Classical.choose_spec ((checked_len_add_spec a b).1 h)).2

/-- When the sum fits, `checked_len_add` returns `Ok` of it. -/
theorem checkedLenAddRes_fits (a b : Std.Usize) (h : a.val + b.val ≤ Usize.max) :
    checkedLenAddRes a b = .Ok (checkedLenAddVal a b) := by
  simp [checkedLenAddRes, h]

/-- Rewrite `checkedLenAddRes a b` to `.Ok _` everywhere when the sum is provably within `Usize.max`. -/
macro "fits_rw" : tactic => `(tactic| try simp (disch := scalar_tac) only [checkedLenAddRes_fits] at *)

/-- `checked_len_add` returns `Ok r` only for the exact sum. -/
theorem checkedLenAddRes_ok (a b r : Std.Usize) (h : checkedLenAddRes a b = .Ok r) :
    r.val = a.val + b.val ∧ a.val + b.val ≤ Usize.max := by
  unfold checkedLenAddRes at h
  split at h
  · rename_i hf; cases h; exact ⟨checkedLenAddVal_val a b hf, hf⟩
  · cases h

@[spec]
theorem len_add_triple (a b : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ len_add a b ⦃ ⇓ r => ⌜ r = lenAddVal a b ⌝ ⦄ := by
  rw [len_add_ok]; mvcgen

@[spec]
theorem checked_len_add_triple (a b : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ checked_len_add a b ⦃ ⇓ r => ⌜ r = checkedLenAddRes a b ⌝ ⦄ := by
  rw [checked_len_add_ok]; mvcgen

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

/-- Close the `Err` (`?` break) branches of a round-trip proof: the trait-level post of
`spec.X.post arg res` holds vacuously on `Err`. Other goals are left untouched. -/
syntax "close_err_branches " ident term:max : tactic
macro_rules
  | `(tactic| close_err_branches $post:ident $arg:term) =>
    `(tactic| all_goals (apply try_break_vc
                         intros
                         mvcgen
                         intro _
                         show (do let a ← ($post $arg (core.result.Result.Err _)); pure (a = true)).holds
                         simp only [$post:ident]
                         mvcgen
                         rename_i hne
                         intro h
                         exact absurd h hne))

/-- Close the `Err` (`?` break) branches of a round-trip proof whose post demands `Ok`
(`is_ok_and`): the hypotheses of such a branch contradict it (e.g. a total content spec
`∃ v, r = Ok v ∧ …` against `r = Err e`). Goals not closed this way are left untouched. -/
macro "close_err_absurd" : tactic =>
  `(tactic| all_goals (first | (apply try_break_vc; intro _ _; exfalso; simp_all; done) | skip))

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

/-- The 2-bit length prefix (in the top bits of the first byte) of a varint of `L` bytes. -/
def varint.pfx (L : Nat) : Nat := if L = 1 then 0 else if L = 2 then 64 else if L = 4 then 128 else 192

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

/-- A total triple with post `True` gives an `ok` value. -/
theorem triple_true_ok {α : Type} {m : RustM α}
    (h : ⦃ ⌜ True ⌝ ⦄ m ⦃ ⇓ _ => ⌜ True ⌝ ⦄) : ∃ v, m = .ok v := by
  cases m <;> simp [Triple, WP.wp, PredTrans.apply] at h ⊢


/-- A total triple from panic freedom and a partial triple. -/
theorem total_of_pf_partial {α : Type} {m : RustM α} {P : α → Prop}
    (hpf : ⦃ ⌜ True ⌝ ⦄ m ⦃ ⇓ _ => ⌜ True ⌝ ⦄) (h : ⦃ ⌜ True ⌝ ⦄ m ⦃ ⇓? r => ⌜ P r ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄ m ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  obtain ⟨v, hv⟩ := triple_true_ok hpf
  have hP := ok_of_partial_triple h hv
  rw [hv]
  apply RustM.ok_spec
  exact hP

/-- Conjunction of the posts of two total triples. -/
theorem triple_and {α : Type} {m : RustM α} {P Q : α → Prop}
    (hP : ⦃ ⌜ True ⌝ ⦄ m ⦃ ⇓ r => ⌜ P r ⌝ ⦄) (hQ : ⦃ ⌜ True ⌝ ⦄ m ⦃ ⇓ r => ⌜ Q r ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄ m ⦃ ⇓ r => ⌜ P r ∧ Q r ⌝ ⦄ := by
  obtain ⟨v, hv, hp⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp hP
  obtain ⟨w, hw, hq⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp hQ
  rw [hv] at hw
  cases hw
  rw [hv]
  apply RustM.ok_spec
  exact ⟨hp, hq⟩

/-- Weakening the post of a total triple. -/
theorem triple_post_mono {α : Type} {m : RustM α} {P Q : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ m ⦃ ⇓ r => ⌜ P r ⌝ ⦄) (hPQ : ∀ r, P r → Q r) :
    ⦃ ⌜ True ⌝ ⦄ m ⦃ ⇓ r => ⌜ Q r ⌝ ⦄ := by
  obtain ⟨v, hv, hP⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp h
  rw [hv]
  apply RustM.ok_spec
  exact hPQ v hP


/-- A total triple is a partial one. -/
theorem partial_of_total {α : Type} {m : RustM α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ m ⦃ ⇓ r => ⌜ P r ⌝ ⦄) : ⦃ ⌜ True ⌝ ⦄ m ⦃ ⇓? r => ⌜ P r ⌝ ⦄ := by
  obtain ⟨v, hv, hP⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp h
  exact partial_triple_of_ok fun r hr => by rw [hv] at hr; cases hr; exact hP

/-- A total triple gives panic freedom. -/
theorem pf_of_total {α : Type} {m : RustM α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ m ⦃ ⇓ r => ⌜ P r ⌝ ⦄) : ⦃ ⌜ True ⌝ ⦄ m ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  obtain ⟨v, hv, _⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp h
  rw [hv]
  apply RustM.ok_spec
  trivial


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

/-- `calculate_value` on contents: the value is the low 6 bits and the length encodes the top 2 bits
(`pfx l = byte / 64 * 64`). -/
theorem varint.calculate_value_content (byte : Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ varint.calculate_value byte
    ⦃ ⇓ r => ⌜ ∃ v l : Std.Usize, r = .Ok (v, l) ∧ v.val = byte.val % 64 ∧
        (l.val = 1 ∨ l.val = 2 ∨ l.val = 4 ∨ l.val = 8) ∧ varint.pfx l.val = byte.val / 64 * 64 ⌝ ⦄ := by
  have := System.Platform.numBits_eq
  have hand : (byte &&& 63#u8).val = byte.val % 64 := by
    have : (byte &&& 63#u8).val = byte.val &&& 63 := by simp
    rw [this]; exact Nat.and_two_pow_sub_one_eq_mod byte.val 6
  have hc8 : ∀ x : Std.U8, (UScalar.cast UScalarTy.Usize x).val = x.val := by
    intro x
    have hx : x.val < 256 := by scalar_tac
    rw [UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    exact lt_of_lt_of_le hx (by rcases this with h | h <;> simp [UScalarTy.Usize_numBits_eq, h])
  mvcgen [varint.calculate_value, varint.TlsVarInt.MAX_LOG]
  · exfalso; scalar_tac
  · rename_i rv hrv rb ha1 ha2 ha3 rl hrl hu hle hgt hl
    have : rl.val = byte.val / 64 := by rw [hrl, hc8, ha1, Nat.shiftRight_eq_div_pow]; rfl
    refine ⟨_, _, rfl, by rw [hrv, hc8, hand], by simp, ?_⟩
    simp [varint.pfx]; omega
  · rename_i rv hrv rb ha1 ha2 ha3 rl hrl hu hle hgt hl
    have : rl.val = byte.val / 64 := by rw [hrl, hc8, ha1, Nat.shiftRight_eq_div_pow]; rfl
    refine ⟨_, _, rfl, by rw [hrv, hc8, hand], by simp, ?_⟩
    simp [varint.pfx]; omega
  · rename_i rv hrv rb ha1 ha2 ha3 rl hrl hu hle hgt hl
    have : rl.val = byte.val / 64 := by rw [hrl, hc8, ha1, Nat.shiftRight_eq_div_pow]; rfl
    refine ⟨_, _, rfl, by rw [hrv, hc8, hand], by simp, ?_⟩
    simp [varint.pfx]; omega
  · rename_i rv hrv rb ha1 ha2 ha3 rl hrl hu hle hgt hl
    have : rl.val = byte.val / 64 := by rw [hrl, hc8, ha1, Nat.shiftRight_eq_div_pow]; rfl
    refine ⟨_, _, rfl, by rw [hrv, hc8, hand], by simp, ?_⟩
    simp [varint.pfx]; omega
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

/-- One iteration of the `TlsVarInt::tls_deserialize_bytes` loop, on contents. -/
theorem varint.deserialize_loop.body_content (len : Std.Usize) (remainder : Slice Std.U8)
    (value : Std.U64) (i : Std.Usize) (hi : 1 ≤ i.val) (hil : i.val ≤ len.val) (hl : len.val ≤ 8)
    (hv : value.val < 2 ^ (8 * i.val - 2)) :
    ⦃ ⌜ True ⌝ ⦄
    varint.TlsVarInt.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes_loop.body len remainder value i
    ⦃ ⇓ r => ⌜ match r with
      | .done (r', v', f) => (f = core.option.Option.None → i = len ∧ r' = remainder ∧ v' = value)
      | .cont (r', v', i') => r'.val.length + 1 = remainder.val.length ∧ i'.val = i.val + 1 ∧
          i'.val ≤ len.val ∧ v'.val < 2 ^ (8 * i'.val - 2) ∧
          ∃ b : Std.U8, remainder.val = b :: r'.val ∧ v'.val = value.val * 256 + b.val ⌝ ⦄ := by
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
    refine ⟨by omega, by scalar_tac, by scalar_tac, ?_, ?_⟩
    · have : r.val = i.val + 1 := by scalar_tac
      rw [this]
      scalar_tac
    · have hpp := core.result.Result.Ok.inj hpt
      cases hbr : remainder.val with
      | nil => rw [hbr] at hrl; simp at hrl
      | cons b l =>
        rw [hbr] at ha
        simp only [List.take_succ_cons, List.take_zero] at ha
        have hp1 : p.1 = b := by rw [hpp]; exact U8_from_be_bytes_of_val a b ha
        refine ⟨b, by simp, ?_⟩
        have h64 : U64.size = 2 ^ 64 := by simp [U64.size, U64.numBits]
        have h8 : (8#i32).toNat = 8 := rfl
        rw [h1, h3, h2, hp1, h64, h8]
        have := hb.1
        simp only [Nat.shiftLeft_eq] at this ⊢
        omega
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

/-- The `TlsVarInt::tls_deserialize_bytes` loop, on contents: without failure it consumes `len - i`
bytes and folds them (big-endian) into the value. -/
theorem varint.deserialize_loop_content (remainder : Slice Std.U8) (len : Std.Usize)
    (value : Std.U64) (i : Std.Usize) (hi : 1 ≤ i.val) (hil : i.val ≤ len.val) (hl : len.val ≤ 8)
    (hv : value.val < 2 ^ (8 * i.val - 2)) :
    ⦃ ⌜ True ⌝ ⦄
    varint.TlsVarInt.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes_loop remainder len value i
    ⦃ ⇓ r => ⌜ r.2.2 = core.option.Option.None → len.val - i.val ≤ remainder.val.length ∧
        r.1.val = remainder.val.drop (len.val - i.val) ∧
        r.2.1.val = (remainder.val.take (len.val - i.val)).foldl (fun a b => a * 256 + b.val) value.val ⌝ ⦄ := by
  unfold varint.TlsVarInt.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes_loop
  apply Aeneas.Std.WP.spec_to_mvcgen
  apply Aeneas.Std.loop.spec_decr_nat
    (fun x : Slice Std.U8 × Std.U64 × Std.Usize => len.val - x.2.2.val)
    (fun x : Slice Std.U8 × Std.U64 × Std.Usize =>
      1 ≤ x.2.2.val ∧ i.val ≤ x.2.2.val ∧ x.2.2.val ≤ len.val ∧ x.2.1.val < 2 ^ (8 * x.2.2.val - 2) ∧
      x.2.2.val - i.val ≤ remainder.val.length ∧ x.1.val = remainder.val.drop (x.2.2.val - i.val) ∧
      x.2.1.val = (remainder.val.take (x.2.2.val - i.val)).foldl (fun a b => a * 256 + b.val) value.val)
    (fun y : Slice Std.U8 × Std.U64 × (core.option.Option Error) => y.2.2 = core.option.Option.None →
        len.val - i.val ≤ remainder.val.length ∧ y.1.val = remainder.val.drop (len.val - i.val) ∧
        y.2.1.val = (remainder.val.take (len.val - i.val)).foldl (fun a b => a * 256 + b.val) value.val)
  · rintro ⟨b, v, j⟩ ⟨hj1, hij, hjl, hjv, hjlen, hjb, hjv'⟩
    dsimp only at hj1 hij hjl hjv hjlen hjb hjv'
    obtain ⟨r, hr, hP⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp
      (varint.deserialize_loop.body_content len b v j hj1 hjl hl hjv)
    dsimp only
    rw [hr, Aeneas.Std.WP.spec_ok]
    cases r with
    | done y =>
      obtain ⟨r', v', f⟩ := y
      intro hf
      obtain ⟨h1, h2, h3⟩ := hP hf
      subst h2; subst h3
      have : j.val = len.val := by rw [h1]
      rw [← this]
      exact ⟨hjlen, hjb, hjv'⟩
    | cont x =>
      obtain ⟨b', v', j'⟩ := x
      obtain ⟨h1, h2, h3, h4, c, hc, hvc⟩ := hP
      dsimp only at h1 h2 h3 h4 hc hvc ⊢
      refine ⟨⟨by omega, by omega, h3, h4, ?_, ?_, ?_⟩, by omega⟩
      · rw [hjb] at hc
        have := congrArg List.length hc
        simp only [List.length_drop, List.length_cons] at this
        omega
      · rw [hjb] at hc
        rw [show j'.val - i.val = (j.val - i.val) + 1 by omega, ← List.drop_drop, hc]
        rfl
      · rw [hjb] at hc
        rw [show j'.val - i.val = (j.val - i.val) + 1 by omega, List.take_add, hc, List.foldl_append,
          ← hjv']
        simp [hvc]
  · exact ⟨hi, le_refl _, hil, hv, by simp, by simp, by simp⟩

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

/-- `check_min_len` succeeds on a value at most `MAX` and its minimal length. -/
theorem varint.check_min_len_total (value : Std.U64) (len : Std.Usize)
    (hv : value.val ≤ 2 ^ 62 - 1) (hl : len.val = varint.lenOf value.val) :
    ⦃ ⌜ True ⌝ ⦄ varint.check_min_len value len ⦃ ⇓ r => ⌜ r = .Ok () ⌝ ⦄ := by
  mvcgen [varint.check_min_len]
  · rename_i r1 hP cf v hx hcf r hne hr
    rw [continue_eq_tryCF] at hcf
    rw [hcf] at hP
    obtain ⟨rfl, -⟩ := hP
    have h := varint.lenOf_char _ _ hr
    have hne' : r ≠ len := by simpa using hne
    exact absurd (UScalar.eq_of_val_eq (by omega)) hne'
  · rename_i r1 hP cf resid hx
    intro hb
    exfalso
    cases r1 with
    | Ok v => simp [tryCF] at hb
    | Err e => omega

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

/-- Content-level `calculate_value` result gives the plain one. -/
theorem varint.calculate_value_content_char {byte : Std.U8} {r : core.result.Result (Std.Usize × Std.Usize) Error}
    (h : ∃ v l : Std.Usize, r = .Ok (v, l) ∧ v.val = byte.val % 64 ∧
        (l.val = 1 ∨ l.val = 2 ∨ l.val = 4 ∨ l.val = 8) ∧ varint.pfx l.val = byte.val / 64 * 64) :
    ∃ v l : Std.Usize, r = .Ok (v, l) ∧ v.val < 64 ∧
        (l.val = 1 ∨ l.val = 2 ∨ l.val = 4 ∨ l.val = 8) := by
  obtain ⟨v, l, h1, h2, h3, _⟩ := h
  exact ⟨v, l, h1, by omega, h3⟩

/-- `TlsVarInt::tls_deserialize_bytes` on contents: on success the input is `b0 :: l`, the length
`L` is the minimal one for the value and matches the prefix of `b0`, and the value is the big-endian
fold of the low 6 bits of `b0` and the next `L - 1` bytes. -/
theorem varint.TlsVarInt.deserialize_content (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ varint.TlsVarInt.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : varint.TlsVarInt) (t : Slice Std.U8), r = .Ok (v, t) →
        ∃ (b0 : Std.U8) (l : List Std.U8) (L : Nat), bytes.val = b0 :: l ∧
          (L = 1 ∨ L = 2 ∨ L = 4 ∨ L = 8) ∧ L = varint.lenOf v.val ∧ varint.pfx L = b0.val / 64 * 64 ∧
          L - 1 ≤ l.length ∧ t.val = l.drop (L - 1) ∧
          v.val = (l.take (L - 1)).foldl (fun a b => a * 256 + b.val) (b0.val % 64) ∧
          v.val ≤ 2 ^ 62 - 1 ⌝ ⦄ := by
  mvcgen [varint.TlsVarInt.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes,
    U8_deserialize_char, varint.calculate_value_content, varint.check_min_len_char,
    varint.deserialize_loop_content, core.result.Result.map_err_spec,
    varint.DeserializeBytesTlsVarInt.tls_deserialize_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError.call_once]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  · rename_i r0 hP r1 p x1 r2 hvl r3 val x2 r4 hcast t ha r5 val1 x3 hr0 hr2 hr4
    have := varint.calculate_value_ok (varint.calculate_value_content_char hvl) hr2
    scalar_tac
  · rename_i r0 hP r1 p x1 r2 hvl r3 val x2 r4 hcast t ha r5 val1 x3 hr0 hr2 hr4
    have := varint.calculate_value_ok (varint.calculate_value_content_char hvl) hr2
    scalar_tac
  · rename_i r0 hP r1 p x1 r2 hvl r3 val x2 r4 hcast t ha r5 val1 x3 hr0 hr2 hr4
    have h64 := (varint.calculate_value_ok (varint.calculate_value_content_char hvl) hr2).1
    rw [hcast] at ha
    have ht := core.result.Result.Ok.inj ha
    have hv1 := core.result.Result.Ok.inj hr4
    subst hv1; subst ht
    scalar_tac
  · rename_i r0 hP r1 p x1 r2 hvl r3 val x2 r4 hcast t ha r5 val1 x3 rl xn hloop r6 hchk r7 u x4 hr0 hr2 hr4 hr6
    intro v t' hvt
    obtain ⟨hv, ht⟩ := Prod.mk.inj (core.result.Result.Ok.inj hvt)
    subst hv; subst ht
    obtain ⟨l, hbl, hp2⟩ := U8_deserialize_ok hP (by rw [hr0]; rfl)
    obtain ⟨v0, l0, h1, h2, h3, h4⟩ := hvl
    rw [hr2] at h1
    have hval := core.result.Result.Ok.inj h1
    subst hval
    have hc := hchk hr6
    have hlp := hloop xn
    have e1 := core.result.Result.Ok.inj (hcast.symm.trans ha)
    have e2 := core.result.Result.Ok.inj hr4
    have hv1 : val1.val = p.1.val % 64 := by
      rw [← e2, ← e1, UScalar.cast_val_eq]
      have : v0.val < 64 := by omega
      simp only [UScalarTy.U64_numBits_eq]
      exact (Nat.mod_eq_of_lt (by omega)).trans h2
    have h1' : (1#usize).val = 1 := by simp
    obtain ⟨hl1, hl2, hl3⟩ := hlp
    simp only [hp2, h1', hv1] at hl1 hl2 hl3
    have hcl : l0.val = lenOf rl.2.1.val := hc.2
    exact ⟨p.1, l, l0.val, hbl, h3, hcl, h4, hl1, hl2, hl3, hc.1⟩
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
      U8.Insts.Tls_codecSize.tls_serialized_len, len_add_ok] at hinv ⊢
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
        have := lenAddVal_val a 1#usize (by scalar_tac)
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
    Shared0Slice.size_closure_map_spec, len_add_triple]
  · subst_vars; scalar_tac
  · rename_i it hit n hn rc hrc rm hrm l hl sum
    intro hsum
    subst hit
    cases rc with
    | Ok c =>
      obtain ⟨u, rfl, hul⟩ := hrm.1 c rfl
      simp only at hl hrc
      subst hl
      have hle : varint.lenOf c.val ≤ 8 := by unfold varint.lenOf; split_ifs <;> omega
      have hsv := lenAddVal_val n l (by scalar_tac)
      rw [if_pos (by scalar_tac)]
      have hc : c.val = it.val.length := by scalar_tac
      rw [hsum, hsv, hul, hc]
      scalar_tac
    | Err e =>
      obtain rfl := hrm.2 e rfl
      simp only at hl hrc
      subst hl
      have hsv := lenAddVal_val n 0#usize (by scalar_tac)
      rw [if_neg (by scalar_tac)]
      rw [hsum]
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

/-- `TlsByteVecU8::tls_serialized_len` is the payload length plus the one-byte length prefix (when
that does not overflow `usize`). -/
theorem tls_vec.TlsByteVecU8.serialized_len_char (self : tls_vec.TlsByteVecU8)
    (h : self.vec.val.length + 1 ≤ Std.Usize.max) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU8.Insts.Tls_codecSize.tls_serialized_len self
    ⦃ ⇓ r => ⌜ r.val = self.vec.val.length + 1 ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU8.Insts.Tls_codecSize.tls_serialized_len,
    tls_vec.TlsByteVecU8.tls_serialized_byte_length, tls_vec.TlsByteVecU8.as_slice,
    CoreModels.core.slice.Slice.len_spec]
  rename_i s hs n hn r
  intro hr
  subst hs; subst hn
  have e := lenAddVal_val (Slice.len self.vec) 1#usize (by scalar_tac)
  subst hr
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
  rename_i s hs n hn r
  intro hr
  subst hs; subst hn
  have e := lenAddVal_val (Slice.len self.vec) 2#usize (by scalar_tac)
  subst hr
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
  rename_i s hs n hn r
  intro hr
  subst hs; subst hn
  have e := lenAddVal_val (Slice.len self.vec) 3#usize (by scalar_tac)
  subst hr
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
  rename_i s hs n hn r
  intro hr
  subst hs; subst hn
  have e := lenAddVal_val (Slice.len self.vec) 4#usize (by scalar_tac)
  subst hr
  scalar_tac

/-- `usize::from(U24)` does not panic (64-bit `usize`, `numBits_eq_64`). -/
theorem Usize.Insts.CoreConvertFromU24.from_pf (value : U24) :
    ⦃ ⌜ True ⌝ ⦄ Usize.Insts.CoreConvertFromU24.from value ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  have := numBits_eq_64
  mvcgen [Usize.Insts.CoreConvertFromU24.from, FromUsizeU24.from.LEN,
    core.mem.size_of_Usize_spec, core.Array.Insts.CoreOpsIndexIndexMut.index_mut,
    core.array.Array.as_mut_slice, rust_primitives.slice.array_as_mut_slice,
    core.slice.Slice.copy_from_slice_U8_total, core.num.Usize.from_be_bytes,
    rust_primitives.arithmetic.from_be_bytes_usize]
  · rename_i bytes0 n hn i1 hi1 hle
    have : (Std.Array.to_slice_mut bytes0).1.length = 8 := by
      simp [Std.Array.to_slice_mut, Std.Array.to_slice, bytes0]
    scalar_tac
  · rename_i bytes0 n hn i1 hi1 hle p back hp
    obtain ⟨hp1, _⟩ := hp
    have hl2 : (Std.Array.to_slice value).val.length = 3 := by simp [Std.Array.to_slice]
    have hl1 : p.1.val.length = 8 - i1.val := by
      rw [hp1]; simp [Std.Array.to_slice_mut, Std.Array.to_slice, bytes0]
    rw [hl1, hl2]
    scalar_tac
  all_goals (exfalso; scalar_tac)

/-- `usize::from(U24)`, when it returns: the big-endian value of the three bytes (partial form, see `Usize.Insts.CoreConvertFromU24.from_char`). -/
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

/-- The three low bytes of the 8 big-endian bytes of a value below `2^24` (64-bit `usize`). -/
theorem usize_low3_bytes (value : Std.Usize) (h64 : System.Platform.numBits = 64)
    (hval : value.val ≤ 16777215) (n : Nat) (hn : n * 8 = 64) :
    ∃ b0 b1 b2 : Std.U8, List.drop (n - 3) (List.map (@UScalar.mk UScalarTy.U8)
        (BitVec.setWidth 64 value.bv).toBEBytes) = [b0, b1, b2] ∧
      value.val = b0.val * 65536 + b1.val * 256 + b2.val := by
  have hn8 : n - 3 = 5 := by omega
  rw [hn8]
  have hvlt : value.val < 2 ^ 64 := by
    show value.bv.toNat < 2 ^ 64
    exact Nat.lt_of_lt_of_le value.bv.isLt (by rw [h64])
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, hbl⟩ :=
    list_eq_eight (BitVec.setWidth 64 value.bv).toBEBytes
      (by simp)
  have hnat : value.val = (BitVec.fromBEBytes [c0, c1, c2, c3, c4, c5, c6, c7]).toNat := by
    have h := fromBEBytes_toBEBytes_toNat (w := 64) (by norm_num) (BitVec.setWidth 64 value.bv)
    rw [hbl, BitVec.toNat_setWidth] at h
    rw [h]
    exact (Nat.mod_eq_of_lt hvlt).symm
  rw [fromBEBytes_eight_toNat] at hnat
  exact ⟨UScalar.mk c5, UScalar.mk c6, UScalar.mk c7, by rw [hbl]; rfl, by
    show value.val = c5.toNat * 65536 + c6.toNat * 256 + c7.toNat
    exact eight_bytes_low3 _ _ _ _ _ _ _ _ _ c0.isLt c1.isLt c2.isLt c3.isLt c4.isLt c5.isLt c6.isLt
      c7.isLt hval hnat⟩

/-- `U24::try_from(usize)` never panics: `Ok` of the three low bytes when the value fits, `Err LibraryError` otherwise. -/
theorem U24.Insts.CoreConvertTryFromUsizeError.try_from_char (value : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ U24.Insts.CoreConvertTryFromUsizeError.try_from value
    ⦃ ⇓ r => ⌜ (value.val ≤ 16777215 → ∃ (a : U24) (b0 b1 b2 : Std.U8), r = .Ok a ∧
          a.val = [b0, b1, b2] ∧ value.val = b0.val * 65536 + b1.val * 256 + b2.val) ∧
        (16777215 < value.val → r = .Err Error.LibraryError) ⌝ ⦄ := by
  have := numBits_eq_64
  mvcgen [U24.Insts.CoreConvertTryFromUsizeError.try_from, TryFromU24UsizeError.try_from.LEN,
    core.mem.size_of_Usize_spec, core.num.Usize.to_be_bytes,
    rust_primitives.arithmetic.to_be_bytes_usize,
    core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from_spec]
  · simp_all [Usize.size, Usize.numBits, UScalarTy.numBits, Nat.shiftLeft_eq]
  · intro h1 _
    obtain ⟨t, ht, htv⟩ := h1 (by simp [Std.Array.to_slice]; scalar_tac)
    have hl : t.val.length = 3 := by rw [htv]; simp [Std.Array.to_slice]; scalar_tac
    refine ⟨t, ht, ?_⟩
    simp only [PostCond.ok]
    mvcgen [core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from_spec,
      Error.Insts.CoreConvertFromTryFromSliceError.from]
    · simp_all [tryCF, Usize.size, Usize.numBits, UScalarTy.numBits, Nat.shiftLeft_eq]
      obtain ⟨a, ha, hav⟩ := ‹∃ a, _ ∧ _›
      subst ha
      simp_all
      obtain ⟨b0, b1, b2, hb, hv⟩ := usize_low3_bytes value this ‹_› _ ‹_ * 8 = 64›
      exact ⟨b0, b1, b2, hb, hv⟩
    · simp_all [tryCF]
      obtain ⟨a, ha, -⟩ := ‹∃ a, _ ∧ _›
      simp [ha]
  all_goals (exfalso; scalar_tac)

/-- `usize::from(U24)` is the big-endian value of the three bytes (total: `Usize.Insts.CoreConvertFromU24.from_pf`). -/
theorem Usize.Insts.CoreConvertFromU24.from_char (value : U24) :
    ⦃ ⌜ True ⌝ ⦄ Usize.Insts.CoreConvertFromU24.from value
    ⦃ ⇓ r => ⌜ ∀ b0 b1 b2 : Std.U8, value.val = [b0, b1, b2] →
        r.val = b0.val * 65536 + b1.val * 256 + b2.val ⌝ ⦄ :=
  total_of_pf_partial (Usize.Insts.CoreConvertFromU24.from_pf value)
    (Usize.Insts.CoreConvertFromU24.from_content value)

/-- `usize::try_from(U24)` through the blanket `TryFrom` impl for `Into` never fails: it is
`Ok` of the big-endian value of the three bytes. -/
theorem core.convert.TryFromTUInfallible.Blanket.try_from_Usize_U24_content (x : U24) :
    ⦃ ⌜ True ⌝ ⦄
    core.convert.TryFromTUInfallible.Blanket.try_from
      (core.convert.Into.Blanket Usize.Insts.CoreConvertFromU24) x
    ⦃ ⇓ r => ⌜ ∃ y, r = .Ok y ∧ ∀ b0 b1 b2 : Std.U8, x.val = [b0, b1, b2] →
        y.val = b0.val * 65536 + b1.val * 256 + b2.val ⌝ ⦄ := by
  unfold core.convert.TryFromTUInfallible.Blanket.try_from core.convert.Into.Blanket
  mvcgen [core.convert.Into.Blanket.into, Usize.Insts.CoreConvertFromU24.from_char]
  exact ⟨_, rfl, ‹_›⟩

/-- `usize::try_from(U24)` (blanket `Into` impl) never fails. -/
theorem core.convert.TryFromTUInfallible.Blanket.try_from_Usize_U24_ok (x : U24) :
    ⦃ ⌜ True ⌝ ⦄
    core.convert.TryFromTUInfallible.Blanket.try_from
      (core.convert.Into.Blanket Usize.Insts.CoreConvertFromU24) x
    ⦃ ⇓ r => ⌜ ∃ y, r = .Ok y ⌝ ⦄ :=
  triple_post_mono (core.convert.TryFromTUInfallible.Blanket.try_from_Usize_U24_content x)
    fun _ ⟨y, hy, _⟩ => ⟨y, hy⟩

/-! ### Hand-translated opaque bodies (`Assumptions/FunsExternal.lean`)

`Assumptions/` is compiled before `Extraction/Funs.lean`, so the hand-written bodies of
`get_content_lengths`, `<&[T]>::tls_serialize_bytes` and `<Box<T>>::tls_deserialize_bytes`
call verbatim copies (`tls_codec.Copied.*`) of the crate functions they need. Each copy is
equal to its original; rewrite with these to reuse the originals' specs. -/

namespace Copied
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

/-- `hbody` obligation of `loop_len_sum_spec` for the `try_fold` loop of `get_content_lengths`.
The loop body is the same for every `TlsByteVecU*` width. (It cannot be stated as a lemma: the
restated body gets different `match` auxiliary definitions and `exact` fails, so the script is shared as a macro.) -/
macro "glen_hbody" : tactic => `(tactic| (
  intro it a ha
  mvcgen [core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
    Copied.U8.Insts.Tls_codecSize.tls_serialized_len, checked_len_add_triple]
  all_goals (fits_rw; simp_all [tryCF, -List.length_eq_zero_iff]; try first | scalar_tac | (have := checkedLenAddVal_val a 1#usize (by scalar_tac); scalar_tac))))

/-- `hk` continuation of the `get_content_lengths` proofs for the plain-`MAX` widths: `max` is the
`core.num.U*.MAX` constant, `rmax` the matching `U*.rMax`, `w` the prefix width. -/
macro "glen_hk " max:term:max rmax:term:max w:term:max : tactic => `(tactic| (
  rintro r ⟨v, rfl, hv⟩
  mvcgen [checked_len_add_triple]
  all_goals (simp_all [tryCF, $max:term, $rmax:term]; try fits_rw; try simp_all [tryCF])
  all_goals try (intro h; split at h <;> simp_all)
  all_goals try (mvcgen [core.convert.From.Blanket.from_spec]; try simp [PostCond.ok])
  all_goals first | scalar_tac | (have := checkedLenAddVal_val v $w (by scalar_tac); scalar_tac)))

/-- `get_content_lengths` of a `TlsByteVecU8` never fails (an over-long vector gives `Err`); an `Ok` result is `(len + 1, len)` with `len ≤ 255`. -/
theorem tls_vec.TlsByteVecU8.get_content_lengths_char (self : tls_vec.TlsByteVecU8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU8.get_content_lengths self
    ⦃ ⇓ r => ⌜ ∀ p : Std.Usize × Std.Usize, r = .Ok p → p.2.val = self.vec.val.length ∧
        p.1.val = self.vec.val.length + 1 ∧ self.vec.val.length ≤ 255 ⌝ ⦄ := by
  unfold tls_vec.TlsByteVecU8.get_content_lengths
  simp only [deref_vec_ok, slice_iter_ok]
  erw [bind_tc_ok, bind_tc_ok]
  refine triple_bind_of_total (loop_len_sum_spec 1#usize _ 0#usize _ ?hlen ?hbody) ?hk
  case hlen => scalar_tac
  case hk => glen_hk core.num.U8.MAX U8.rMax 1#usize
  case hbody => glen_hbody


/-- `get_content_lengths` of a `TlsByteVecU16` never fails (an over-long vector gives `Err`); an `Ok` result is `(len + 2, len)` with `len ≤ 65535`. -/
theorem tls_vec.TlsByteVecU16.get_content_lengths_char (self : tls_vec.TlsByteVecU16) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU16.get_content_lengths self
    ⦃ ⇓ r => ⌜ ∀ p : Std.Usize × Std.Usize, r = .Ok p → p.2.val = self.vec.val.length ∧
        p.1.val = self.vec.val.length + 2 ∧ self.vec.val.length ≤ 65535 ⌝ ⦄ := by
  unfold tls_vec.TlsByteVecU16.get_content_lengths
  simp only [deref_vec_ok, slice_iter_ok]
  erw [bind_tc_ok, bind_tc_ok]
  refine triple_bind_of_total (loop_len_sum_spec 1#usize _ 0#usize _ ?hlen ?hbody) ?hk
  case hlen => scalar_tac
  case hk => glen_hk core.num.U16.MAX U16.rMax 2#usize
  case hbody => glen_hbody



/-- `get_content_lengths` of a `TlsByteVecU32` never fails (an over-long vector gives `Err`); an `Ok` result is `(len + 4, len)` with `len ≤ 2^32 - 1`. -/
theorem tls_vec.TlsByteVecU32.get_content_lengths_char (self : tls_vec.TlsByteVecU32) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU32.get_content_lengths self
    ⦃ ⇓ r => ⌜ ∀ p : Std.Usize × Std.Usize, r = .Ok p → p.2.val = self.vec.val.length ∧
        p.1.val = self.vec.val.length + 4 ∧ self.vec.val.length ≤ 4294967295 ⌝ ⦄ := by
  unfold tls_vec.TlsByteVecU32.get_content_lengths
  simp only [deref_vec_ok, slice_iter_ok]
  erw [bind_tc_ok, bind_tc_ok]
  refine triple_bind_of_total (loop_len_sum_spec 1#usize _ 0#usize _ ?hlen ?hbody) ?hk
  case hlen => scalar_tac
  case hk => have := numBits_eq_64; glen_hk core.num.U32.MAX U32.rMax 4#usize
  case hbody => glen_hbody


/-- The bytes of `U24::MAX`. -/
theorem U24.MAX_val : U24.MAX.val = [255#u8, 255#u8, 255#u8] := by
  unfold U24.MAX
  simp [Std.Array.repeat]

/-- `get_content_lengths` of a `TlsByteVecU24` never fails (an over-long vector gives `Err`); an `Ok` result is `(len + 3, len)` with `len ≤ 2^24 - 1`. -/
theorem tls_vec.TlsByteVecU24.get_content_lengths_char (self : tls_vec.TlsByteVecU24) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU24.get_content_lengths self
    ⦃ ⇓ r => ⌜ ∀ p : Std.Usize × Std.Usize, r = .Ok p → p.2.val = self.vec.val.length ∧
        p.1.val = self.vec.val.length + 3 ∧ self.vec.val.length ≤ 16777215 ⌝ ⦄ := by
  unfold tls_vec.TlsByteVecU24.get_content_lengths
  simp only [deref_vec_ok, slice_iter_ok]
  erw [bind_tc_ok, bind_tc_ok]
  refine triple_bind_of_total (loop_len_sum_spec 1#usize _ 0#usize _ ?hlen ?hbody) ?hk
  case hlen => scalar_tac
  case hk =>
    rintro r ⟨v, rfl, hv⟩
    have hmax : ∀ y : Std.Usize, (∀ b0 b1 b2 : Std.U8, U24.MAX.val = [b0, b1, b2] →
        y.val = b0.val * 65536 + b1.val * 256 + b2.val) → y.val = 16777215 := by
      intro y h
      have := h 255#u8 255#u8 255#u8 U24.MAX_val
      simpa using this
    simp only [Copied.Usize.Insts.CoreConvertFromU24_eq, Copied.U24.MAX_eq]
    mvcgen [checked_len_add_triple, core.convert.TryFromTUInfallible.Blanket.try_from_Usize_U24_content,
      core.result.Result.unwrap_ok_spec]
    try_vcs
    · obtain ⟨y, hy, -⟩ := ‹∃ y, _ = core.result.Result.Ok y ∧ _›
      exact ⟨y, hy⟩
    · obtain ⟨y, hy, hh⟩ := ‹∃ y, _ = core.result.Result.Ok y ∧ _›
      have hr := hmax y hh
      clear hmax hh
      simp_all [tryCF, -List.length_eq_zero_iff]
    · obtain ⟨y, hy, hh⟩ := ‹∃ y, _ = core.result.Result.Ok y ∧ _›
      have hr := hmax y hh
      clear hmax hh
      simp_all [tryCF, -List.length_eq_zero_iff]
      fits_rw
      simp_all
      have := checkedLenAddVal_val v 3#usize (by scalar_tac)
      scalar_tac
    · intro _
      clear hmax
      simp [PostCond.ok]
  case hbody => glen_hbody

/-! ### `TlsByteVecU*::serialize_bytes_bytes` (uses the hand-written `get_content_lengths`)

`_partial`: if it returns `Ok out`, then `out` has the payload plus the prefix and the payload is within the
prefix bound (it panics above, in the model of the `debug_assert!`). `_char`: below the bound it does not panic. -/

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

/-- A successful `checked_alloc_len` is the exact sum. -/
theorem checked_alloc_len_ok (a b : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ checked_alloc_len a b
    ⦃ ⇓ r => ⌜ ∀ n : Std.Usize, r = .Ok n → n.val = a.val + b.val ⌝ ⦄ := by
  mvcgen [checked_alloc_len, checked_capacity, CoreModels.core.num.Usize.saturating_add_spec]
  · simp
  · rename_i sat hsat hle
    intro n hn
    simp only [core.result.Result.Ok.injEq] at hn
    subst hn hsat
    have hm := Usize.hcast_Isize_MAX_val
    have h1 := UScalar.saturating_add_val a b
    scalar_tac

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

/-- Closing script shared by the `TlsByteVecU*.serialize_bytes_bytes_{partial,char,content}` proofs: discharge the VCs left by `mvcgen`. The `first` alternatives are the union over all widths (partial/char arithmetic, content equation for U8, U16/U32 and U24). -/
macro "bytevec_ser_close" : tactic => `(tactic| (
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
    | exact ⟨_, ‹_›, rfl⟩
    | (obtain ⟨b0, b1, b2, h3, h4⟩ := ‹∃ b0 b1 b2, _ ∧ _›; exact ⟨b0, b1, b2, h4.symm, by rw [h3]; rfl⟩)
    | (intro _ out h; cases h)))

/-- `TlsByteVecU8::serialize_bytes_bytes`, when it returns `Ok`, gives the payload plus the 1-byte prefix, and the payload is within the prefix bound. -/
theorem tls_vec.TlsByteVecU8.serialize_bytes_bytes_partial (self : tls_vec.TlsByteVecU8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU8.serialize_bytes_bytes self
    ⦃ ⇓? r => ⌜ ∀ out : alloc.vec.Vec Std.U8, r = .Ok out →
        out.val.length = self.vec.val.length + 1 ∧ self.vec.val.length ≤ 255 ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU8.serialize_bytes_bytes,
    tls_vec.TlsByteVecU8.get_content_lengths_char,
    checked_alloc_len_total, alloc.vec.Vec.extend_from_slice_U8_spec,
    core.U8.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from_char,
    alloc.vec.Vec.with_capacity, core.result.Result.unwrap_ok_spec, U8_serialize_char,
    alloc.vec.Vec.len_spec, tls_vec.TlsByteVecU8.as_slice, CoreModels.core.slice.Slice.len_spec,
    tls_vec.TlsByteVecU8.assert_written_bytes_total]
  bytevec_ser_close

/-- `TlsByteVecU8::serialize_bytes_bytes` does not panic (an over-long vector gives `Err`); an `Ok` result has the payload length plus the 1-byte prefix. -/
theorem tls_vec.TlsByteVecU8.serialize_bytes_bytes_char (self : tls_vec.TlsByteVecU8) :
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
  bytevec_ser_close

/-- `TlsByteVecU16::serialize_bytes_bytes`, when it returns `Ok`, gives the payload plus the 2-byte prefix, and the payload is within the prefix bound. -/
theorem tls_vec.TlsByteVecU16.serialize_bytes_bytes_partial (self : tls_vec.TlsByteVecU16) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU16.serialize_bytes_bytes self
    ⦃ ⇓? r => ⌜ ∀ out : alloc.vec.Vec Std.U8, r = .Ok out →
        out.val.length = self.vec.val.length + 2 ∧ self.vec.val.length ≤ 65535 ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU16.serialize_bytes_bytes,
    tls_vec.TlsByteVecU16.get_content_lengths_char,
    checked_alloc_len_total, alloc.vec.Vec.extend_from_slice_U8_spec,
    core.U16.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from_char,
    alloc.vec.Vec.with_capacity, core.result.Result.unwrap_ok_spec, U16_serialize_char,
    alloc.vec.Vec.len_spec, tls_vec.TlsByteVecU16.as_slice, CoreModels.core.slice.Slice.len_spec,
    tls_vec.TlsByteVecU16.assert_written_bytes_total]
  bytevec_ser_close

/-- `TlsByteVecU16::serialize_bytes_bytes` does not panic (an over-long vector gives `Err`); an `Ok` result has the payload length plus the 2-byte prefix. -/
theorem tls_vec.TlsByteVecU16.serialize_bytes_bytes_char (self : tls_vec.TlsByteVecU16) :
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
  bytevec_ser_close

/-- `TlsByteVecU24::serialize_bytes_bytes` does not panic (an over-long vector gives `Err`); an `Ok` result has the payload length plus the 3-byte prefix. -/
theorem tls_vec.TlsByteVecU24.serialize_bytes_bytes_char (self : tls_vec.TlsByteVecU24) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU24.serialize_bytes_bytes self
    ⦃ ⇓ r => ⌜ ∀ out : alloc.vec.Vec Std.U8, r = .Ok out →
        out.val.length = self.vec.val.length + 3 ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU24.serialize_bytes_bytes,
    tls_vec.TlsByteVecU24.get_content_lengths_char,
    checked_alloc_len_total, alloc.vec.Vec.extend_from_slice_U8_spec,
    U24.Insts.CoreConvertTryFromUsizeError.try_from_char,
    alloc.vec.Vec.with_capacity, core.result.Result.unwrap_ok_spec, U24_serialize_char,
    alloc.vec.Vec.len_spec, tls_vec.TlsByteVecU24.as_slice, CoreModels.core.slice.Slice.len_spec,
    tls_vec.TlsByteVecU24.assert_written_bytes_total]
  bytevec_ser_close

/-- `TlsByteVecU24::serialize_bytes_bytes`, when it returns `Ok`, gives the payload plus the 3-byte prefix. -/
theorem tls_vec.TlsByteVecU24.serialize_bytes_bytes_partial (self : tls_vec.TlsByteVecU24) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU24.serialize_bytes_bytes self
    ⦃ ⇓? r => ⌜ ∀ out : alloc.vec.Vec Std.U8, r = .Ok out →
        out.val.length = self.vec.val.length + 3 ⌝ ⦄ :=
  partial_of_total (tls_vec.TlsByteVecU24.serialize_bytes_bytes_char self)

/-- `TlsByteVecU32::serialize_bytes_bytes`, when it returns `Ok`, gives the payload plus the 4-byte prefix, and the payload is within the prefix bound. -/
theorem tls_vec.TlsByteVecU32.serialize_bytes_bytes_partial (self : tls_vec.TlsByteVecU32) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU32.serialize_bytes_bytes self
    ⦃ ⇓? r => ⌜ ∀ out : alloc.vec.Vec Std.U8, r = .Ok out →
        out.val.length = self.vec.val.length + 4 ∧ self.vec.val.length ≤ 4294967295 ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU32.serialize_bytes_bytes,
    tls_vec.TlsByteVecU32.get_content_lengths_char,
    checked_alloc_len_total, alloc.vec.Vec.extend_from_slice_U8_spec,
    core.U32.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from_char,
    alloc.vec.Vec.with_capacity, core.result.Result.unwrap_ok_spec, U32_serialize_char,
    alloc.vec.Vec.len_spec, tls_vec.TlsByteVecU32.as_slice, CoreModels.core.slice.Slice.len_spec,
    tls_vec.TlsByteVecU32.assert_written_bytes_total]
  bytevec_ser_close

/-- `TlsByteVecU32::serialize_bytes_bytes` does not panic (an over-long vector gives `Err`); an `Ok` result has the payload length plus the 4-byte prefix. -/
theorem tls_vec.TlsByteVecU32.serialize_bytes_bytes_char (self : tls_vec.TlsByteVecU32) :
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
  bytevec_ser_close

/-- `TlsByteVecU8::serialize_bytes_bytes`, when it returns `Ok`, gives the 1-byte length prefix followed by the payload. -/
theorem tls_vec.TlsByteVecU8.serialize_bytes_bytes_content (self : tls_vec.TlsByteVecU8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU8.serialize_bytes_bytes self
    ⦃ ⇓? r => ⌜ ∀ out : alloc.vec.Vec Std.U8, r = .Ok out →
        ∃ n : Std.U8, n.val = self.vec.val.length ∧ out.val = n :: self.vec.val ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU8.serialize_bytes_bytes,
    tls_vec.TlsByteVecU8.get_content_lengths_char,
    checked_alloc_len_total, alloc.vec.Vec.extend_from_slice_U8_spec,
    core.U8.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from_char,
    alloc.vec.Vec.with_capacity, core.result.Result.unwrap_ok_spec, U8_serialize_char,
    alloc.vec.Vec.len_spec, tls_vec.TlsByteVecU8.as_slice, CoreModels.core.slice.Slice.len_spec,
    tls_vec.TlsByteVecU8.assert_written_bytes_total]
  bytevec_ser_close

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

/-- `Vec::eq` does not fail when the element `eq` does not fail (total). -/
theorem alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq_pf {T : Type}
    (inst : core.cmp.PartialEq T T) (a b : alloc.vec.Vec T)
    (heq : ∀ x y, ⦃ ⌜ True ⌝ ⦄ inst.eq x y ⦃ ⇓ _ => ⌜ True ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq inst a b ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  have hbody : ∀ (it : core.ops.range.Range Std.Usize) (res : Bool),
      it.end.val = a.val.length → a.val.length = b.val.length → it.start.val ≤ it.end.val →
      ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq_loop.body inst a b it res
      ⦃ ⇓ r => ⌜ match r with
        | .done _ => True
        | .cont (it', _) => (it'.end.val = a.val.length ∧ it'.start.val ≤ it'.end.val) ∧
            it'.end.val - it'.start.val < it.end.val - it.start.val ⌝ ⦄ := by
    intro it res hend hlen hle
    unfold alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq_loop.body
    mvcgen [heq, core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next_Usize_spec] <;>
      first | trivial | grind
  have hloop : ∀ (it : core.ops.range.Range Std.Usize) (res : Bool),
      it.end.val = a.val.length → a.val.length = b.val.length → it.start.val ≤ it.end.val →
      ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq_loop inst it a b res
      ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
    intro it res hend hlen hle
    unfold alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq_loop
    apply Aeneas.Std.WP.spec_to_mvcgen
    apply Aeneas.Std.loop.spec_decr_nat
      (fun p : core.ops.range.Range Std.Usize × Bool => p.1.end.val - p.1.start.val)
      (fun p : core.ops.range.Range Std.Usize × Bool =>
        p.1.end.val = a.val.length ∧ p.1.start.val ≤ p.1.end.val)
      (fun _ => True)
    · rintro ⟨it', res'⟩ ⟨hp1, hp2⟩
      obtain ⟨v, hv, hP⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp (hbody it' res' hp1 hlen hp2)
      show Aeneas.Std.WP.spec (alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq_loop.body inst a b it' res') _
      rw [hv, Aeneas.Std.WP.spec_ok]
      cases v <;> exact hP
    · exact ⟨hend, hle⟩
  unfold alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq
  mvcgen
  · rename_i r1 h1 r2 h2
    intro h3
    subst h1 h2
    have h := hloop { start := 0#usize, «end» := Slice.len a } true (by simp [Slice.len])
      (by scalar_tac) (by simp [Slice.len])
    exact h trivial

/-- The parent `eq` of an `Eq`-lawful instance does not fail. -/
theorem _root_.CoreModels.core.cmp.Eq.Lawful.eq_pf {T : Type} {inst : core.cmp.Eq T}
    (h : core.cmp.Eq.Lawful T inst) (x y : T) :
    ⦃ ⌜ True ⌝ ⦄ inst.PartialEqInst.eq x y ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  have hs := h.eq_spec x y
  mvcgen [hs]

/-- `Vec::eq`, when the element `eq` decides `=`, decides `=`. -/
theorem alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq_iff {T : Type}
    (inst : core.cmp.PartialEq T T) (a b : alloc.vec.Vec T)
    (heq : ∀ x y, ⦃ ⌜ True ⌝ ⦄ inst.eq x y ⦃ ⇓ r => ⌜ r = true ↔ x = y ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq inst a b
    ⦃ ⇓ r => ⌜ r = true ↔ a = b ⌝ ⦄ := by
  classical
  have hdec : ∀ x y, ⦃ ⌜ True ⌝ ⦄ inst.eq x y ⦃ ⇓ r => ⌜ r = decide (x = y) ⌝ ⦄ := by
    intro x y
    have h := heq x y
    mvcgen [h]
    intro hr
    rw [Bool.eq_iff_iff, hr]
    simp
  have h := alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq_spec inst a b hdec
  mvcgen [h]
  rintro rfl
  simp [Subtype.val_inj]
  rfl

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

/-- `VLBytes::eq`: `decide` of equality of the contents. -/
@[spec] theorem quic_vec.VLBytes.Insts.CoreCmpPartialEqVLBytes.eq_decide_spec
    (a b : quic_vec.VLBytes) :
    ⦃ ⌜ True ⌝ ⦄ quic_vec.VLBytes.Insts.CoreCmpPartialEqVLBytes.eq a b
    ⦃ ⇓ r => ⌜ r = decide (a.vec.val = b.vec.val) ⌝ ⦄ := by
  unfold quic_vec.VLBytes.Insts.CoreCmpPartialEqVLBytes.eq
  mvcgen

/-- `PartialEq for u16`, in the `decide` form that the generic `Vec::eq` spec takes. -/
theorem core.U16.Insts.CoreCmpPartialEqU16.eq_decide_spec (x y : Std.U16) :
    ⦃ ⌜ True ⌝ ⦄ core.U16.Insts.CoreCmpPartialEqU16.eq x y ⦃ ⇓ r => ⌜ r = decide (x = y) ⌝ ⦄ := by
  simp only [core.U16.Insts.CoreCmpPartialEqU16]; mvcgen
  by_cases h : x = y <;> simp [h]

/-- `Vec<u16>::eq`: `decide` of list equality. -/
@[spec] theorem alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq_U16_spec (a b : alloc.vec.Vec Std.U16) :
    ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq core.U16.Insts.CoreCmpPartialEqU16 a b
    ⦃ ⇓ r => ⌜ r = decide (a.val = b.val) ⌝ ⦄ :=
  alloc.vec.Vec.Insts.CoreCmpPartialEqVec.eq_spec _ a b
    core.U16.Insts.CoreCmpPartialEqU16.eq_decide_spec

/-- `TlsByteVecU16::serialize_bytes_bytes`, when it returns `Ok`, gives the 2-byte length prefix followed by the payload. -/
theorem tls_vec.TlsByteVecU16.serialize_bytes_bytes_content (self : tls_vec.TlsByteVecU16) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU16.serialize_bytes_bytes self
    ⦃ ⇓? r => ⌜ ∀ out : alloc.vec.Vec Std.U8, r = .Ok out →
        ∃ n : Std.U16, n.val = self.vec.val.length ∧
          out.val = (Aeneas.Std.core.num.U16.to_be_bytes n).val ++ self.vec.val ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU16.serialize_bytes_bytes,
    tls_vec.TlsByteVecU16.get_content_lengths_char,
    checked_alloc_len_total, alloc.vec.Vec.extend_from_slice_U8_spec,
    core.U16.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from_char,
    alloc.vec.Vec.with_capacity, core.result.Result.unwrap_ok_spec, U16_serialize_char,
    alloc.vec.Vec.len_spec, tls_vec.TlsByteVecU16.as_slice, CoreModels.core.slice.Slice.len_spec,
    tls_vec.TlsByteVecU16.assert_written_bytes_total]
  bytevec_ser_close

/-- `TlsByteVecU32::serialize_bytes_bytes`, when it returns `Ok`, gives the 4-byte length prefix followed by the payload. -/
theorem tls_vec.TlsByteVecU32.serialize_bytes_bytes_content (self : tls_vec.TlsByteVecU32) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU32.serialize_bytes_bytes self
    ⦃ ⇓? r => ⌜ ∀ out : alloc.vec.Vec Std.U8, r = .Ok out →
        ∃ n : Std.U32, n.val = self.vec.val.length ∧
          out.val = (Aeneas.Std.core.num.U32.to_be_bytes n).val ++ self.vec.val ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU32.serialize_bytes_bytes,
    tls_vec.TlsByteVecU32.get_content_lengths_char,
    checked_alloc_len_total, alloc.vec.Vec.extend_from_slice_U8_spec,
    core.U32.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from_char,
    alloc.vec.Vec.with_capacity, core.result.Result.unwrap_ok_spec, U32_serialize_char,
    alloc.vec.Vec.len_spec, tls_vec.TlsByteVecU32.as_slice, CoreModels.core.slice.Slice.len_spec,
    tls_vec.TlsByteVecU32.assert_written_bytes_total]
  bytevec_ser_close

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

/-- `TlsByteVecU24::serialize_bytes_bytes`, when it returns `Ok`, gives the 3-byte length prefix followed by the payload. -/
theorem tls_vec.TlsByteVecU24.serialize_bytes_bytes_content (self : tls_vec.TlsByteVecU24) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU24.serialize_bytes_bytes self
    ⦃ ⇓? r => ⌜ ∀ out : alloc.vec.Vec Std.U8, r = .Ok out →
        ∃ b0 b1 b2 : Std.U8, b0.val * 65536 + b1.val * 256 + b2.val = self.vec.val.length ∧
          out.val = b0 :: b1 :: b2 :: self.vec.val ⌝ ⦄ := by
  mvcgen [tls_vec.TlsByteVecU24.serialize_bytes_bytes,
    tls_vec.TlsByteVecU24.get_content_lengths_char,
    checked_alloc_len_total, alloc.vec.Vec.extend_from_slice_U8_spec,
    U24.Insts.CoreConvertTryFromUsizeError.try_from_char,
    alloc.vec.Vec.with_capacity, core.result.Result.unwrap_ok_spec, U24_serialize_char,
    alloc.vec.Vec.len_spec, tls_vec.TlsByteVecU24.as_slice, CoreModels.core.slice.Slice.len_spec,
    tls_vec.TlsByteVecU24.assert_written_bytes_total]
  bytevec_ser_close

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
      U8.Insts.Tls_codecSize.tls_serialized_len, checked_len_add_triple]
    all_goals (fits_rw; simp_all [tryCF, -List.length_eq_zero_iff]; try first | scalar_tac | (have := checkedLenAddVal_val a 1#usize (by scalar_tac); scalar_tac))
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


/-! ### `Vec::clone` does not fail, given that the element `clone` does not -/

theorem vecCloneLoop_pf {T : Type} (inst : core.clone.Clone T)
    (hc : ∀ x, ⦃ ⌜ True ⌝ ⦄ inst.clone x ⦃ ⇓ _ => ⌜ True ⌝ ⦄)
    (it : core.slice.iter.Iter T) (w : rust_primitives.sequence.Seq T)
    (h : (w : Slice T).val.length + (it : Slice T).val.length ≤ Usize.max) :
    ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.Insts.CoreCloneClone.clone_loop inst it w
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  unfold alloc.vec.Vec.Insts.CoreCloneClone.clone_loop
  apply Aeneas.Std.WP.spec_to_mvcgen
  apply Aeneas.Std.loop.spec_decr_nat
    (fun p : core.slice.iter.Iter T × rust_primitives.sequence.Seq T => (p.1 : Slice T).val.length)
    (fun p : core.slice.iter.Iter T × rust_primitives.sequence.Seq T =>
      (p.2 : Slice T).val.length + (p.1 : Slice T).val.length ≤ Usize.max)
  · rintro ⟨it, w⟩ hinv
    simp only [alloc.vec.Vec.Insts.CoreCloneClone.clone_loop.body,
      core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
      rust_primitives.sequence.seq_len, rust_primitives.sequence.seq_remove,
      rust_primitives.sequence.seq_push]
    simp only at hinv
    by_cases hz : Slice.len it = 0#usize
    · simp [hz]
    · have hpos : 0 < (it : Slice T).val.length := by scalar_tac
      have hw : (w : Slice T).val.length < Usize.max := by omega
      simp [hz, hpos]
      obtain ⟨r, hr, -⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp (hc ((it : Slice T).val[0]))
      simp [hr, hw]
      omega
  · exact h

theorem vecClone_pf {T : Type} (inst : core.clone.Clone T)
    (hc : ∀ x, ⦃ ⌜ True ⌝ ⦄ inst.clone x ⦃ ⇓ _ => ⌜ True ⌝ ⦄) (v : alloc.vec.Vec T) :
    ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.Insts.CoreCloneClone.clone inst v ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  unfold alloc.vec.Vec.Insts.CoreCloneClone.clone
  simp only [alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref, alloc.vec.Vec.as_slice,
    core.slice.Slice.iter, rust_primitives.sequence.seq_empty,
    rust_primitives.sequence.seq_to_slice, rust_primitives.sequence.seq_from_slice]
  have hl := vecCloneLoop_pf inst hc
  mvcgen [hl]
  simp [Slice.new]; scalar_tac

/-- Folding a slice iterator with a never-failing `call_mut` never fails. -/
theorem Shared0Slice.fold_pf {T C : Type}
    (inst : core.ops.function.FnMut C (Std.Usize × T) Std.Usize)
    (h : ∀ c p, ⦃ ⌜ True ⌝ ⦄ inst.call_mut c p ⦃ ⇓ _ => ⌜ True ⌝ ⦄)
    (it : core.slice.iter.Iter T) (acc : Std.Usize) (c : C) :
    ⦃ ⌜ True ⌝ ⦄
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold inst it acc c
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  simp only [core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold,
    core.iter.traits.iterator.Iterator.fold.default, core.iter.traits.iterator.iter_fold,
    core.iter.traits.iterator.iter_fold_loop]
  apply Aeneas.Std.WP.spec_to_mvcgen
  apply Aeneas.Std.loop.spec_decr_nat
    (fun p : core.slice.iter.Iter T × C × Std.Usize => (p.1 : Slice T).val.length)
    (fun _ => True)
  · rintro ⟨it', c', a⟩ _
    simp only [core.iter.traits.iterator.iter_fold_loop.body,
      core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
      rust_primitives.sequence.seq_len, rust_primitives.sequence.seq_remove]
    by_cases hz : Slice.len it' = 0#usize
    · simp [hz]
    · have hpos : 0 < (it' : Slice T).val.length := by
        rcases Nat.eq_zero_or_pos (it' : Slice T).val.length with h0 | h0
        · exfalso; apply hz; apply UScalar.eq_of_val_eq; simp [Slice.len, h0]
        · exact h0
      obtain ⟨⟨a1, f1⟩, hv⟩ := triple_true_ok (h c' (a, (it' : Slice T).val[0]))
      simp [hz, hpos, hv]
  · trivial

/-- `<&[T]>::tls_serialized_len` does not fail when the element size does not. -/
theorem Shared0Slice.size_pf {T : Type} (SizeInst : Size T)
    (SizeInstLawful : Size.Lawful T SizeInst) (self_ : Slice T) :
    ⦃ ⌜ True ⌝ ⦄ Shared0Slice.Insts.Tls_codecSize.tls_serialized_len SizeInst self_
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  have hcall : ∀ c p, ⦃ ⌜ True ⌝ ⦄
      (quic_vec.SizeShared0Slice.tls_serialized_len.closure.Insts.CoreOpsFunctionFnMutPairUsizeSharedTUsize
        SizeInst).call_mut c p ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
    rintro c ⟨a, e⟩
    have hs := SizeInstLawful.tls_serialized_len_spec
    mvcgen [quic_vec.SizeShared0Slice.tls_serialized_len.closure.Insts.CoreOpsFunctionFnMutPairUsizeSharedTUsize.call_mut,
      hs]
  have hl := Shared0Slice.fold_pf _ hcall
  have hm := Shared0Slice.size_closure_map_spec SizeInst
  mvcgen [Shared0Slice.Insts.Tls_codecSize.tls_serialized_len, hl, hm]

/-- `Vec<T>::tls_serialized_len` does not fail when the element size does not. -/
theorem alloc.vec.Vec.size_pf {T : Type} (SizeInst : Size T)
    (SizeInstLawful : Size.Lawful T SizeInst) (self_ : alloc.vec.Vec T) :
    ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.Insts.Tls_codecSize.tls_serialized_len SizeInst self_
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  have hl := Shared0Slice.size_pf SizeInst SizeInstLawful
  mvcgen [alloc.vec.Vec.Insts.Tls_codecSize.tls_serialized_len, hl]

/-! ### `DeserializeBytes::tls_deserialize_exact_bytes` (trait default) -/

/-- The default `tls_deserialize_exact_bytes` does not fail when `tls_deserialize_bytes` does not. -/
theorem DeserializeBytes.exact_default_pf {Self : Type} (inst : DeserializeBytes Self)
    (h : ∀ b, ⦃ ⌜ True ⌝ ⦄ inst.tls_deserialize_bytes b ⦃ ⇓ _ => ⌜ True ⌝ ⦄)
    (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ DeserializeBytes.tls_deserialize_exact_bytes.default inst bytes
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  have hb := h bytes
  mvcgen [DeserializeBytes.tls_deserialize_exact_bytes.default, hb]
  rename_i r _ residual _
  intro hx
  cases r <;> simp only [tls_codec.tryCF, reduceCtorEq, core.ops.control_flow.ControlFlow.Break.injEq] at hx
  subst hx
  refine ⟨_, rfl, ?_⟩
  mvcgen

/-- The default `tls_deserialize_exact_bytes` meets its post given the post of
`tls_deserialize_bytes` (on the `ok` outcomes). -/
theorem DeserializeBytes.exact_default_fc {Self : Type} (inst : DeserializeBytes Self)
    (bytes : Slice Std.U8)
    (h : ⦃ ⌜ True ⌝ ⦄ inst.tls_deserialize_bytes bytes
      ⦃ ⇓? res => ⌜ (DeserializeBytes.tls_deserialize_bytes.post inst.SizeInst inst bytes res).holds ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄ DeserializeBytes.tls_deserialize_exact_bytes.default inst bytes
    ⦃ ⇓? res => ⌜ (DeserializeBytes.tls_deserialize_exact_bytes.post inst.SizeInst inst bytes res).holds ⌝ ⦄ := by
  apply partial_triple_of_ok
  intro r hr
  unfold DeserializeBytes.tls_deserialize_exact_bytes.default at hr
  have hl : ∀ (rem : Slice Std.U8), core.slice.Slice.len rem = ok (Slice.len rem) := by
    intro rem; unfold core.slice.Slice.len; rfl
  cases hd : inst.tls_deserialize_bytes bytes with
  | ok r0 =>
    have hp := ok_of_partial_triple h hd
    rw [hd] at hr
    cases r0 with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
        core.convert.From.Blanket.from] at hr
      subst hr
      simp [DeserializeBytes.tls_deserialize_exact_bytes.post, core.result.Result.is_err, RustM.holds]
      mvcgen
    | Ok p =>
      obtain ⟨o, rem⟩ := p
      simp [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
        core.slice.Slice.is_empty, hl] at hr
      by_cases h0 : Slice.len rem = 0#usize
      · rw [if_pos h0] at hr
        have := ok.inj hr
        subst this
        simp only [DeserializeBytes.tls_deserialize_bytes.post, core.result.Result.is_err,
          core.result.Result.is_ok_and,
          __4.ensures.closure.Insts.CoreOpsFunctionFnOnceTuplePairSelf_SharedSliceU8Bool,
          __4.ensures.closure.Insts.CoreOpsFunctionFnOnceTuplePairSelf_SharedSliceU8Bool.call_once,
          DeserializeBytes.tls_deserialize_exact_bytes.post,
          __5.ensures.closure.Insts.CoreOpsFunctionFnOnceTupleSelf_Bool,
          __5.ensures.closure.Insts.CoreOpsFunctionFnOnceTupleSelf_Bool.call_once, hl] at hp ⊢
        have hz : (↑rem : List U8).length = 0 := by
          have := congrArg UScalar.val h0
          simpa [Slice.len] using this
        cases hL : inst.SizeInst.tls_serialized_len o with
        | ok i2 =>
          simp [hL, hz] at hp ⊢
          rw [h0] at hp
          have h1 : (0#usize + i2 : RustM Usize) = ok i2 := by
            have := Aeneas.Std.UScalar.add_equiv (0#usize) i2
            cases hc : (0#usize + i2 : RustM Usize) with
            | ok z =>
              rw [hc] at this
              obtain ⟨_, hz, _⟩ := this
              congr 1
              apply UScalar.eq_of_val_eq
              simpa using hz
            | fail e =>
              rw [hc] at this
              exfalso
              apply this.2
              scalar_tac
            | div => rw [hc] at this; exact this.elim
          simp [h1] at hp
          exact hp
        | fail e => simp [hL, hz, RustM.holds] at hp ⊢; exact hp
        | div => simp [hL, hz, RustM.holds] at hp ⊢; exact hp
      · rw [if_neg h0] at hr
        have := ok.inj hr
        subst this
        simp [DeserializeBytes.tls_deserialize_exact_bytes.post, core.result.Result.is_err, RustM.holds]
        mvcgen
  | fail e => rw [hd] at hr; simp at hr
  | div => rw [hd] at hr; simp at hr

/-! ### Trait-level `tls_deserialize_bytes` post from a characterization of the result -/

/-- An `Err` result meets the trait-level post of `tls_deserialize_bytes`. -/
theorem DeserializeBytes.post_err {Self : Type} (SizeInst : Size Self) (inst : DeserializeBytes Self)
    (bytes : Slice Std.U8) (e : Error) :
    (DeserializeBytes.tls_deserialize_bytes.post SizeInst inst bytes (.Err e)).holds := by
  simp [DeserializeBytes.tls_deserialize_bytes.post, core.result.Result.is_err, RustM.holds]
  mvcgen

/-- An `Ok (v, rem)` result meets the trait-level post of `tls_deserialize_bytes` when the size
of `v` is `n` and `rem.len + n = bytes.len`. -/
theorem DeserializeBytes.post_ok {Self : Type} (SizeInst : Size Self) (inst : DeserializeBytes Self)
    (bytes : Slice Std.U8) (v : Self) (rem : Slice Std.U8) (n : Std.Usize)
    (hn : SizeInst.tls_serialized_len v = ok n)
    (hrem : rem.val.length + n.val = bytes.val.length) :
    (DeserializeBytes.tls_deserialize_bytes.post SizeInst inst bytes (.Ok (v, rem))).holds := by
  have hl : ∀ (s : Slice Std.U8), core.slice.Slice.len s = ok (Slice.len s) := by
    intro s; unfold core.slice.Slice.len; rfl
  have hb : bytes.val.length ≤ Std.Usize.max := by
    have := bytes.property; scalar_tac
  have hadd : (Slice.len rem + n : RustM Std.Usize) = ok (Slice.len bytes) := by
    have := Aeneas.Std.UScalar.add_equiv (Slice.len rem) n
    cases hc : (Slice.len rem + n : RustM Std.Usize) with
    | ok z =>
      rw [hc] at this
      obtain ⟨_, hz, _⟩ := this
      congr 1
      apply UScalar.eq_of_val_eq
      simp only [Slice.len_val, Slice.length] at hz ⊢
      omega
    | fail e =>
      rw [hc] at this
      exfalso
      apply this.2
      simp only [Slice.len_val, Slice.length] at *
      scalar_tac
    | div => rw [hc] at this; exact this.elim
  simp only [DeserializeBytes.tls_deserialize_bytes.post, core.result.Result.is_err,
    core.result.Result.is_ok_and,
    __4.ensures.closure.Insts.CoreOpsFunctionFnOnceTuplePairSelf_SharedSliceU8Bool.call_once,
    hl]
  simp [hn, hadd, RustM.holds]
  have hle : (rem.val.length ≤ bytes.val.length) := by omega
  simp only [hle, if_true]
  mvcgen

/-- `String::tls_serialized_len` for a string of at most `2^30 - 1` bytes: the byte length plus its
varint prefix length (as for `<&[u8]>::tls_serialized_len`). -/
theorem alloc.string.String.size_char (t : alloc.string.String)
    (h : (alloc.string.String.utf8U8 t).length ≤ 2 ^ 30 - 1) :
    ⦃ ⌜ True ⌝ ⦄ alloc.string.String.Insts.Tls_codecSize.tls_serialized_len t
    ⦃ ⇓ r => ⌜ r.val = (alloc.string.String.utf8U8 t).length +
        varint.lenOf (alloc.string.String.utf8U8 t).length ⌝ ⦄ := by
  mvcgen [alloc.string.String.Insts.Tls_codecSize.tls_serialized_len, Shared0Slice.size_U8_char]
  rename_i s hs _
  intro hr
  have htake : List.take Usize.max t.utf8U8 = t.utf8U8 := List.take_of_length_le (by scalar_tac)
  rw [htake] at hs
  rw [hr, hs, if_pos h]

/-! ### Trait-level `tls_serialize_bytes` post from a characterization of the result -/

/-- An `Err` result meets the trait-level post of `tls_serialize_bytes`. -/
theorem SerializeBytes.post_err {Self : Type} (SizeInst : Size Self) (inst : SerializeBytes Self)
    (self_ : Self) (e : Error) :
    (SerializeBytes.tls_serialize_bytes.post SizeInst inst self_ (.Err e)).holds := by
  simp [SerializeBytes.tls_serialize_bytes.post, core.result.Result.is_err, RustM.holds]
  mvcgen

/-- An `Ok out` result meets the trait-level post of `tls_serialize_bytes` when the size of `self_`
is `n` and `out.len = n`. -/
theorem SerializeBytes.post_ok {Self : Type} (SizeInst : Size Self) (inst : SerializeBytes Self)
    (self_ : Self) (out : alloc.vec.Vec Std.U8) (n : Std.Usize)
    (hn : SizeInst.tls_serialized_len self_ = ok n)
    (hout : (out : Slice Std.U8).val.length = n.val) :
    (SerializeBytes.tls_serialize_bytes.post SizeInst inst self_ (.Ok out)).holds := by
  have hl : alloc.vec.Vec.len out = ok (Slice.len (out : Slice Std.U8)) := by
    obtain ⟨l, hl, hl'⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp (alloc.vec.Vec.len_spec out)
    rw [hl, hl']
  simp only [SerializeBytes.tls_serialize_bytes.post, core.result.Result.is_err,
    core.result.Result.is_ok_and,
    __3.ensures.closure.Insts.CoreOpsFunctionFnOnceTupleVecU8Bool.call_once, hl, hn]
  have he : Slice.len (out : Slice Std.U8) = n := by
    apply UScalar.eq_of_val_eq
    simpa [Slice.len_val, Slice.length] using hout
  simp [he, RustM.holds]
  mvcgen

/-- `TlsVarInt::tls_serialized_len` is the minimal varint length. -/
theorem varint.TlsVarInt.size_char (v : varint.TlsVarInt) :
    ⦃ ⌜ True ⌝ ⦄ varint.TlsVarInt.Insts.Tls_codecSize.tls_serialized_len v
    ⦃ ⇓ r => ⌜ r.val = varint.lenOf v.val ⌝ ⦄ := by
  mvcgen [varint.TlsVarInt.Insts.Tls_codecSize.tls_serialized_len, varint.TlsVarInt.bytes_len_spec]
  intro h1 h2 h3 h4 h5 h6
  exact (varint.lenOf_char _ _ ⟨h1, h2, h3, h4, h5, h6⟩).1

/-- A trait `pre` that is `ok true` holds (the shape `(do let a ← pre; pure (a = true)).holds` of the
`Lawful` hypotheses): `have hs := fun x => I.m_spec x (pre_holds_of_ok_true rfl)`. -/
theorem pre_holds_of_ok_true {m : RustM Bool} (h : m = ok true) :
    (do let a ← m; pure (a = true) : RustM Prop).holds := by
  subst h
  unfold RustM.holds
  mvcgen

/-- `RustM.holds` of a pure proposition. -/
theorem holds_ok_iff {p : Prop} : (ok p : RustM Prop).holds ↔ p := by
  unfold RustM.holds
  constructor
  · intro h; exact h trivial
  · intro hp; mvcgen

/-- Converse of `SerializeBytes.post_ok`: an `Ok out` meeting the trait-level post of
`tls_serialize_bytes` has the length given by `tls_serialized_len`. -/
theorem SerializeBytes.post_ok_elim {Self : Type} (SizeInst : Size Self) (inst : SerializeBytes Self)
    (self_ : Self) (out : alloc.vec.Vec Std.U8)
    (h : (SerializeBytes.tls_serialize_bytes.post SizeInst inst self_ (.Ok out)).holds) :
    ∃ n, SizeInst.tls_serialized_len self_ = ok n ∧ (out : Slice Std.U8).val.length = n.val := by
  have hl : alloc.vec.Vec.len out = ok (Slice.len (out : Slice Std.U8)) := by
    obtain ⟨l, hl, hl'⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp (alloc.vec.Vec.len_spec out)
    rw [hl, hl']
  simp only [SerializeBytes.tls_serialize_bytes.post, core.result.Result.is_err,
    core.result.Result.is_ok_and,
    __3.ensures.closure.Insts.CoreOpsFunctionFnOnceTupleVecU8Bool.call_once, hl] at h
  cases hn : SizeInst.tls_serialized_len self_ with
  | ok n =>
    refine ⟨n, rfl, ?_⟩
    simp only [hn] at h
    have h2 : decide (Slice.len out = n) = true := holds_ok_iff.mp h
    have h3 := of_decide_eq_true h2
    have := congrArg UScalar.val h3
    simpa [Slice.len_val, Slice.length] using this
  | fail e =>
    exfalso
    have := h trivial
    simp [hn] at this
    simp [Std.Do.wp, Std.Do.PredTrans.apply] at this
  | div =>
    exfalso
    have := h trivial
    simp [hn] at this
    simp [Std.Do.wp, Std.Do.PredTrans.apply] at this

/-- Converse of `DeserializeBytes.post_ok`: an `Ok (v, rem)` meeting the trait-level post of
`tls_deserialize_bytes` has `rem.len + size v = bytes.len`. -/
theorem DeserializeBytes.post_ok_elim {Self : Type} (SizeInst : Size Self) (inst : DeserializeBytes Self)
    (bytes : Slice Std.U8) (v : Self) (rem : Slice Std.U8)
    (h : (DeserializeBytes.tls_deserialize_bytes.post SizeInst inst bytes (.Ok (v, rem))).holds) :
    ∃ n, SizeInst.tls_serialized_len v = ok n ∧ rem.val.length + n.val = bytes.val.length := by
  have hl : ∀ (s : Slice Std.U8), core.slice.Slice.len s = ok (Slice.len s) := by
    intro s; unfold core.slice.Slice.len; rfl
  simp only [DeserializeBytes.tls_deserialize_bytes.post, core.result.Result.is_err,
    core.result.Result.is_ok_and,
    __4.ensures.closure.Insts.CoreOpsFunctionFnOnceTuplePairSelf_SharedSliceU8Bool.call_once,
    hl] at h
  cases hn : SizeInst.tls_serialized_len v with
  | ok n =>
    refine ⟨n, rfl, ?_⟩
    simp [hn] at h
    by_cases hle : (rem.val.length ≤ bytes.val.length)
    · simp only [hle, if_true] at h
      cases hadd : (rem.len + n : RustM Std.Usize) with
      | ok z =>
        have hz := (Aeneas.Std.UScalar.add_equiv (Slice.len rem) n)
        rw [hadd] at hz
        obtain ⟨_, hz, _⟩ := hz
        simp only [hadd] at h
        have h2 : decide (z = Slice.len bytes) = true := holds_ok_iff.mp h
        have h3 := congrArg UScalar.val (of_decide_eq_true h2)
        simp only [Slice.len_val, Slice.length] at hz h3 ⊢
        omega
      | fail e =>
        exfalso
        have := h trivial
        simp [hadd] at this
        simp [Std.Do.wp, Std.Do.PredTrans.apply] at this
      | div =>
        exfalso
        have := h trivial
        simp [hadd] at this
        simp [Std.Do.wp, Std.Do.PredTrans.apply] at this
    · exfalso
      simp only [hle, if_false] at h
      have := holds_ok_iff.mp h
      simp at this
  | fail e =>
    exfalso
    have := h trivial
    simp [hn] at this
    by_cases hle : (rem.val.length ≤ bytes.val.length) <;> simp [hle, Std.Do.wp, Std.Do.PredTrans.apply] at this
  | div =>
    exfalso
    have := h trivial
    simp [hn] at this
    by_cases hle : (rem.val.length ≤ bytes.val.length) <;> simp [hle, Std.Do.wp, Std.Do.PredTrans.apply] at this

/-! ### `Option<T>` serialization, generic over `T` -/

/-- Behaviour of `Option<T>::tls_serialize_bytes` from the trait contracts of `T`: never fails to
terminate, and an `Ok out` is `[0]` for `None` and `1 :: v` for `Some e`, with `v` of the size of `e`. -/
theorem Option_serialize_char {T : Type} (inst : SerializeBytes T)
    (hlaw : SerializeBytes.Lawful T inst) (o : core.option.Option T) :
    ⦃ ⌜ True ⌝ ⦄ core.option.Option.Insts.Tls_codecSerializeBytes.tls_serialize_bytes inst o
    ⦃ ⇓ r => ⌜ (∀ out, r = .Ok out →
        (o = .None ∧ (out : Slice Std.U8).val = [0#u8]) ∨
        ∃ (e : T) (n : Std.Usize) (v : List Std.U8), o = .Some e ∧ inst.SizeInst.tls_serialized_len e = ok n ∧
          v.length = n.val ∧ (out : Slice Std.U8).val = 1#u8 :: v) ∧
        (o = .None → ∃ out, r = .Ok out) ⌝ ⦄ := by
  have hsz := hlaw.SizeInstLawful.tls_serialized_len_spec
  have hs := fun x => hlaw.tls_serialize_bytes_spec x (pre_holds_of_ok_true rfl)
  cases o with
  | none =>
    mvcgen [core.option.Option.Insts.Tls_codecSerializeBytes.tls_serialize_bytes,
      alloc.slice.Slice.into_vec_spec]
    refine ⟨?_, ⟨_, rfl⟩⟩
    intro out hout
    have hout' := core.result.Result.Ok.inj hout
    subst hout'
    refine Or.inl ⟨trivial, ?_⟩
    rename_i hr
    simp [hr, Std.Array.to_slice]
    rfl
  | some e =>
    obtain ⟨n, hn, -⟩ := (Aeneas.Std.WP.triple_iff_exists_ok).1
      (hsz e (pre_holds_of_ok_true rfl))
    mvcgen [core.option.Option.Insts.Tls_codecSerializeBytes.tls_serialize_bytes, hn, hs,
      checked_alloc_len_ok, alloc.vec.Vec.with_capacity, alloc.vec.Vec.append,
      rust_primitives.sequence.seq_concat]
    try_vcs
    all_goals (try simp only [continue_eq_tryCF] at *)
    all_goals (try (intros; simp [PostCond.ok]; done))
    · rename_i _ _ _ _ _ _ hr3 _
      subst hr3
      simp [Slice.new]
      scalar_tac
    · rename_i r5 hchk cf0 val x1 r3 hr3 out1 hout1 r1 hpost cf1 val1 x2 comb hlen hcv hr1
      refine ⟨?_, by simp⟩
      intro out hout
      have hout' := core.result.Result.Ok.inj hout
      subst hout' hr1
      obtain ⟨n', hn', hl⟩ := SerializeBytes.post_ok_elim _ _ _ _ hpost
      have hnn := ok.inj (hn.symm.trans hn')
      subst hnn
      subst hr3
      refine Or.inr ⟨e, n, val1.val, rfl, hn, hl, ?_⟩
      simp [comb, hout1, Slice.new]
    · rename_i r5 hchk cf0 val x1 r3 hr3 out1 hout1 r1 hpost cf1 val1 x2 comb hlen hcv hr1
      exfalso
      subst hr1
      obtain ⟨n', hn', hl⟩ := SerializeBytes.post_ok_elim _ _ _ _ hpost
      have hnn := ok.inj (hn.symm.trans hn')
      subst hnn
      have h1 := hchk val hcv
      subst hr3
      apply hlen
      simp only [comb, hout1, List.length_append, hl]
      simp [Slice.new]
      scalar_tac

/-- Behaviour of `Option<T>::tls_deserialize_bytes` from the trait contracts of `T`: never fails to
terminate, and an `Ok (v, rem)` consumed a `0` tag (`None`) or a `1` tag followed by an `e` of size
`n` (`Some e`), the rest of the input being `rem`. -/
theorem Option_deserialize_char {T : Type} (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ core.option.Option.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes inst bytes
    ⦃ ⇓ r => ⌜ ∀ v rem, r = .Ok (v, rem) → ∃ l,
        (bytes.val = 0#u8 :: l ∧ v = .None ∧ rem.val = l) ∨
        (bytes.val = 1#u8 :: l ∧ ∃ (e : T) (n : Std.Usize), v = .Some e ∧
          inst.SizeInst.tls_serialized_len e = ok n ∧ rem.val.length + n.val = l.length) ⌝ ⦄ := by
  have hd := fun b => hlaw.tls_deserialize_bytes_spec b (pre_holds_of_ok_true rfl)
  mvcgen [core.option.Option.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes,
    U8_deserialize_char, hd]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  all_goals (try (intros; simp [PostCond.ok]; done))
  · rename_i r1 hP cf p hx hz hr1
    intro v rem hv
    obtain ⟨l, hb, hp2⟩ := U8_deserialize_ok hP (continue_eq_tryCF.2 hr1)
    rw [hz] at hb
    simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    exact ⟨l, Or.inl ⟨hb, rfl, hp2⟩⟩
  · rename_i r1 hP cf p hx hz r2 hpost cf2 p2 hx2 hr1 hr2
    intro v rem hv
    obtain ⟨l, hb, hp2⟩ := U8_deserialize_ok hP (continue_eq_tryCF.2 hr1)
    rw [hz] at hb
    obtain ⟨e, rem2⟩ := p2
    subst hr2
    obtain ⟨n, hn, hl⟩ := DeserializeBytes.post_ok_elim _ _ _ _ _ hpost
    simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    exact ⟨l, Or.inr ⟨hb, e, n, rfl, hn, by rw [← hp2]; exact hl⟩⟩
  · intro v rem hv
    exact absurd hv (by simp)

/-! ### Sizes of `Option` / pairs / triples (the `len_add`s of the extracted `tls_serialized_len`) -/

theorem Option_size_none {T : Type} (S : Size T) :
    core.option.Option.Insts.Tls_codecSize.tls_serialized_len S .None = ok (lenAddVal 1#usize 0#usize) := by
  simp [core.option.Option.Insts.Tls_codecSize.tls_serialized_len, len_add_ok]

theorem Option_size_some {T : Type} (S : Size T) (e : T) (n : Std.Usize)
    (h : S.tls_serialized_len e = ok n) :
    core.option.Option.Insts.Tls_codecSize.tls_serialized_len S (.Some e) = ok (lenAddVal 1#usize n) := by
  simp [core.option.Option.Insts.Tls_codecSize.tls_serialized_len, len_add_ok, h]

theorem Pair_size {T U : Type} (S : Size T) (S1 : Size U) (a : T) (b : U) (n1 n2 : Std.Usize)
    (h1 : S.tls_serialized_len a = ok n1) (h2 : S1.tls_serialized_len b = ok n2) :
    Pair.Insts.Tls_codecSize.tls_serialized_len S S1 (a, b) = ok (lenAddVal n1 n2) := by
  simp [Pair.Insts.Tls_codecSize.tls_serialized_len, len_add_ok, h1, h2]

theorem TupleTUV_size {T U V : Type} (S : Size T) (S1 : Size U) (S2 : Size V) (a : T) (b : U) (c : V)
    (n1 n2 n3 : Std.Usize) (h1 : S.tls_serialized_len a = ok n1) (h2 : S1.tls_serialized_len b = ok n2)
    (h3 : S2.tls_serialized_len c = ok n3) :
    TupleTUV.Insts.Tls_codecSize.tls_serialized_len S S1 S2 (a, b, c) =
      ok (lenAddVal (lenAddVal n1 n2) n3) := by
  simp [TupleTUV.Insts.Tls_codecSize.tls_serialized_len, len_add_ok, h1, h2, h3]

/-- `<[T]>::first`: the head of the contents. -/
theorem core.slice.Slice.first_spec {T : Type} (s : Slice T) :
    ⦃ ⌜ True ⌝ ⦄ core.slice.Slice.first s ⦃ ⇓ r => ⌜ r = s.val.head? ⌝ ⦄ := by
  mvcgen [core.slice.Slice.first, rust_primitives.slice.slice_index, Slice.index_usize]
  · rename_i hb hd
    have h0 : s.val.length = 0 := by
      have := congrArg UScalar.val (of_decide_eq_true (hd ▸ hb))
      simpa [Slice.len_val, Slice.length] using this
    simp [List.length_eq_zero_iff.mp h0]
  · rename_i hb hd hg
    exfalso
    apply hb
    rw [hd]
    rw [Slice.getElem?_Usize_eq] at hg
    replace hg : s.val[0]? = none := hg
    have h0 : s.val = [] := by
      cases hs : s.val with
      | nil => rfl
      | cons y l => rw [hs] at hg; simp at hg
    simp [Slice.len, h0]
    rfl
  · rename_i hb hd x hg
    rw [Slice.getElem?_Usize_eq] at hg
    replace hg : s.val[0]? = some x := hg
    cases hs : s.val with
    | nil => rw [hs] at hg; simp at hg
    | cons y l => rw [hs] at hg; simp_all

/-- `Option<&u8>::eq`: `decide` of equality. -/
theorem Option_U8_eq_spec (a b : core.option.Option Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ core.option.Option.Insts.CoreCmpPartialEqOption.eq
      (core.Shared1A.Insts.CoreCmpPartialEqShared0B core.U8.Insts.CoreCmpPartialEqU8) a b
    ⦃ ⇓ r => ⌜ r = decide (a = b) ⌝ ⦄ := by
  apply core.option.Option.Insts.CoreCmpPartialEqOption.eq_spec
  intro x y
  exact core.U8.Insts.CoreCmpPartialEqU8.eq_decide_spec x y

/-! ### `Box<T>` (erased: `Box<T>` is `T`) -/

theorem Box_size {T : Type} (S : Size T) (x : T) (n : Std.Usize) (h : S.tls_serialized_len x = ok n) :
    Box.Insts.Tls_codecSize.tls_serialized_len S x = ok n := by
  simp [Box.Insts.Tls_codecSize.tls_serialized_len, alloc.Box.Insts.CoreConvertAsRef.as_ref, h]

theorem Box_serialize_eq {T : Type} (inst : SerializeBytes T) (x : T) :
    Box.Insts.Tls_codecSerializeBytes.tls_serialize_bytes inst x = inst.tls_serialize_bytes x := by
  simp [Box.Insts.Tls_codecSerializeBytes.tls_serialize_bytes, alloc.Box.Insts.CoreConvertAsRef.as_ref]

theorem Box_deserialize_eq {T : Type} (inst : DeserializeBytes T) (bytes : Slice Std.U8) :
    Box.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes inst bytes = inst.tls_deserialize_bytes bytes := by
  unfold Box.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes
  cases h : inst.tls_deserialize_bytes bytes with
  | ok r => cases r with
    | Ok p => obtain ⟨v, r1⟩ := p; simp
    | Err e => simp
  | fail e => simp
  | div => simp

/-! ### Pairs and triples -/

/-- `(T, U)::tls_deserialize_bytes`, from the trait contracts of `T` and `U`. -/
theorem Pair_deserialize_char {T U : Type} (inst : DeserializeBytes T) (inst1 : DeserializeBytes U)
    (hlaw : DeserializeBytes.Lawful T inst) (hlaw1 : DeserializeBytes.Lawful U inst1)
    (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ Pair.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes inst inst1 bytes
    ⦃ ⇓ r => ⌜ ∀ a b rem, r = .Ok ((a, b), rem) → ∃ n1 n2 : Std.Usize,
        inst.SizeInst.tls_serialized_len a = ok n1 ∧ inst1.SizeInst.tls_serialized_len b = ok n2 ∧
        rem.val.length + n2.val + n1.val = bytes.val.length ⌝ ⦄ := by
  have hd := fun b => hlaw.tls_deserialize_bytes_spec b (pre_holds_of_ok_true rfl)
  have hd1 := fun b => hlaw1.tls_deserialize_bytes_spec b (pre_holds_of_ok_true rfl)
  mvcgen [Pair.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes, hd, hd1]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  all_goals (try (intros; simp [PostCond.ok]; done))
  rename_i r1 h1 cf p x r2 h2 cf2 p2 x2 hr1 hr2
  intro a b rem hv
  obtain ⟨p1a, p1r⟩ := p
  obtain ⟨p2a, p2r⟩ := p2
  subst hr1 hr2
  obtain ⟨n1, hn1, hl1⟩ := DeserializeBytes.post_ok_elim _ _ _ _ _ h1
  obtain ⟨n2, hn2, hl2⟩ := DeserializeBytes.post_ok_elim _ _ _ _ _ h2
  simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at hv
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hv
  dsimp only at hl2
  exact ⟨n1, n2, hn1, hn2, by omega⟩

/-- `(T, U, V)::tls_deserialize_bytes`, from the trait contracts of `T`, `U` and `V`. -/
theorem TupleTUV_deserialize_char {T U V : Type} (inst : DeserializeBytes T)
    (inst1 : DeserializeBytes U) (inst2 : DeserializeBytes V)
    (hlaw : DeserializeBytes.Lawful T inst) (hlaw1 : DeserializeBytes.Lawful U inst1)
    (hlaw2 : DeserializeBytes.Lawful V inst2) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ TupleTUV.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes inst inst1 inst2 bytes
    ⦃ ⇓ r => ⌜ ∀ a b c rem, r = .Ok ((a, b, c), rem) → ∃ n1 n2 n3 : Std.Usize,
        inst.SizeInst.tls_serialized_len a = ok n1 ∧ inst1.SizeInst.tls_serialized_len b = ok n2 ∧
        inst2.SizeInst.tls_serialized_len c = ok n3 ∧
        rem.val.length + n3.val + n2.val + n1.val = bytes.val.length ⌝ ⦄ := by
  have hd := fun b => hlaw.tls_deserialize_bytes_spec b (pre_holds_of_ok_true rfl)
  have hd1 := fun b => hlaw1.tls_deserialize_bytes_spec b (pre_holds_of_ok_true rfl)
  have hd2 := fun b => hlaw2.tls_deserialize_bytes_spec b (pre_holds_of_ok_true rfl)
  mvcgen [TupleTUV.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes, hd, hd1, hd2]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  all_goals (try (intros; simp [PostCond.ok]; done))
  rename_i r1 h1 cf p x r2 h2 cf2 p2 x2 r3 h3 cf3 p3 x3 hr1 hr2 hr3
  intro a b c rem hv
  obtain ⟨p1a, p1r⟩ := p
  obtain ⟨p2a, p2r⟩ := p2
  obtain ⟨p3a, p3r⟩ := p3
  subst hr1 hr2 hr3
  obtain ⟨n1, hn1, hl1⟩ := DeserializeBytes.post_ok_elim _ _ _ _ _ h1
  obtain ⟨n2, hn2, hl2⟩ := DeserializeBytes.post_ok_elim _ _ _ _ _ h2
  obtain ⟨n3, hn3, hl3⟩ := DeserializeBytes.post_ok_elim _ _ _ _ _ h3
  simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at hv
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hv
  dsimp only at hl2 hl3
  exact ⟨n1, n2, n3, hn1, hn2, hn3, by omega⟩

/-! ### `TlsVecU*` / `SecretTlsVecU*` `deserialize_bytes` (loop over the elements)

The size of a vector is a fold of `len_add` (opaque) over the element sizes, starting at the
prefix width `a0`; `SizeFoldRel` is its relational model. The loop invariant `DesLoopInv` ties the
elements read so far to the bytes consumed. Termination: an element that consumes `0` bytes is
rejected by the code itself (`consumed = 0` => error), so `remainder.len` strictly decreases. -/

/-- Relational model of the size fold of a vector: fold of `lenAddVal` of the element sizes. -/
inductive SizeFoldRel {T : Type} (S : Size T) : Std.Usize → List T → Std.Usize → Prop
  | nil (a : Std.Usize) : SizeFoldRel S a [] a
  | cons (a : Std.Usize) (x : T) (l : List T) (n : Std.Usize) (r : Std.Usize) :
      S.tls_serialized_len x = ok n → SizeFoldRel S (lenAddVal a n) l r →
      SizeFoldRel S a (x :: l) r

theorem SizeFoldRel.snoc {T : Type} {S : Size T} {a : Std.Usize} {l : List T} {r : Std.Usize}
    (h : SizeFoldRel S a l r) (e : T) (n : Std.Usize) (hn : S.tls_serialized_len e = ok n) :
    SizeFoldRel S a (l ++ [e]) (lenAddVal r n) := by
  induction h with
  | nil a => exact .cons a e [] n _ hn (.nil _)
  | cons a x l n' r hx _ ih => exact .cons a x _ n' _ hx ih

theorem SizeFoldRel.functional {T : Type} {S : Size T} {a : Std.Usize} {l : List T} {r r' : Std.Usize}
    (h : SizeFoldRel S a l r) (h' : SizeFoldRel S a l r') : r = r' := by
  induction h generalizing r' with
  | nil a => cases h'; rfl
  | cons a x l n r hx _ ih =>
    cases h' with
    | cons _ _ _ n2 _ hx2 h2 =>
      rw [hx] at hx2
      cases hx2
      exact ih h2

theorem size_fold_rel {T C : Type} (S : Size T) (hS : ∀ e, ∃ n, S.tls_serialized_len e = ok n)
    (inst : core.ops.function.FnMut C (Std.Usize × T) Std.Usize)
    (hcall : ∀ c a e n, S.tls_serialized_len e = ok n → inst.call_mut c (a, e) = ok (lenAddVal a n, c))
    (it : core.slice.iter.Iter T) (acc : Std.Usize) (c : C) :
    ⦃ ⌜ True ⌝ ⦄
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold inst it acc c
    ⦃ ⇓ r => ⌜ SizeFoldRel S acc (it : Slice T).val r ⌝ ⦄ := by
  simp only [core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold,
    core.iter.traits.iterator.Iterator.fold.default, core.iter.traits.iterator.iter_fold,
    core.iter.traits.iterator.iter_fold_loop]
  apply Aeneas.Std.WP.spec_to_mvcgen
  apply Aeneas.Std.loop.spec_decr_nat
    (fun p : core.slice.iter.Iter T × C × Std.Usize => (p.1 : Slice T).val.length)
    (fun p => ∀ r, SizeFoldRel S p.2.2 (p.1 : Slice T).val r → SizeFoldRel S acc (it : Slice T).val r)
  · rintro ⟨it', c', a⟩ hinv
    simp only [core.iter.traits.iterator.iter_fold_loop.body,
      core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
      rust_primitives.sequence.seq_len, rust_primitives.sequence.seq_remove] at hinv ⊢
    by_cases hz : Slice.len it' = 0#usize
    · have h0 : (it' : Slice T).val = [] := by
        rw [← List.length_eq_zero_iff]; scalar_tac
      simp only [hz]
      simp
      exact hinv a (by rw [h0]; exact .nil a)
    · have hpos : 0 < (it' : Slice T).val.length := by scalar_tac
      obtain ⟨x, l, hl⟩ : ∃ x l, (it' : Slice T).val = x :: l := by
        cases h : (it' : Slice T).val with
        | nil => rw [h] at hpos; simp at hpos
        | cons y l => exact ⟨y, l, rfl⟩
      obtain ⟨n, hn⟩ := hS x
      simp [hz, hl, hcall _ _ _ _ hn]
      intro r hr
      apply hinv
      rw [hl]
      exact .cons _ _ _ n _ hn hr
  · intro r h; exact h

/-- A lawful `Size` instance never fails. -/
theorem Size.lawful_ok {T : Type} (S : Size T) (hl : Size.Lawful T S) (e : T) :
    ∃ n, S.tls_serialized_len e = ok n := by
  obtain ⟨v, hv, _⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp
    (hl.tls_serialized_len_spec e (pre_holds_of_ok_true rfl))
  exact ⟨v, hv⟩

/-- A lawful `Size` instance never fails (as a spec for `mvcgen`, naming the result). -/
theorem Size.len_char {T : Type} (S : Size T) (hl : Size.Lawful T S) (e : T) :
    ⦃ ⌜ True ⌝ ⦄ S.tls_serialized_len e ⦃ ⇓ r => ⌜ S.tls_serialized_len e = ok r ⌝ ⦄ := by
  obtain ⟨n, hn⟩ := Size.lawful_ok S hl e
  rw [hn]
  apply RustM.ok_spec
  rfl

/-- Invariant of the `deserialize_bytes` loops: `l` are the elements read so far, `a0` the prefix
width, `N` the length of the whole input. -/
def DesLoopInv {T : Type} (S : Size T) (a0 : Std.Usize) (N : Nat) (l : List T)
    (remainder : Slice Std.U8) (read : Std.Usize) : Prop :=
  l.length ≤ read.val ∧ (∃ s, SizeFoldRel S a0 l s ∧ s.val + remainder.val.length = N) ∧
  read.val + remainder.val.length + a0.val = N

/-- The remainder after a successful length-prefix read. -/
theorem prefix_rem {U : Type} (W : Nat) {bytes : Slice Std.U8}
    {r : core.result.Result (U × Slice Std.U8) Error} {p : U × Slice Std.U8}
    (hP : (W ≤ bytes.val.length → ∃ t : Slice Std.U8, t.val = bytes.val.drop W ∧ ∃ x, r = .Ok (x, t)) ∧
      (bytes.val.length < W → r = .Err Error.EndOfStream))
    (hr : r = .Ok p) : p.2.val.length + W = bytes.val.length := by
  by_cases h : W ≤ bytes.val.length
  · obtain ⟨t, ht, x, hx⟩ := hP.1 h
    rw [hx] at hr
    have := core.result.Result.Ok.inj hr
    subst this
    simp [ht]
    omega
  · have := hP.2 (by omega)
    rw [this] at hr
    cases hr

/-! #### Generic `TlsVecU*` / `SecretTlsVecU*` (`TlsVecGen`)

The extracted per-width functions are identical modulo the wrapper type (`structure … where vec`),
the prefix codec and its conversion to `usize`, and the prefix width. They are stated once here
over an abstract wrapper `W` (`vec : W → Vec T`, `mk`, `push`); each width links its concrete
function to the generic one by `rfl` (definitional unfolding; `deserialize_bytes` needs a case split
on the `?` match, and the message literals are existentially quantified so that no `toStr` is
re-elaborated here), and its per-width lemmas are one-line corollaries. -/

namespace TlsVecGen

variable {T W : Type}

/-- The loop body of `TlsVecU*::deserialize_bytes` / `SecretTlsVecU*::deserialize_bytes`, over
an abstract wrapper `W` with its `push` (`msg`: the error message literal). -/
theorem push_spec (vec : W → alloc.vec.Vec T) (mk : alloc.vec.Vec T → W) (hmk : ∀ v, vec (mk v) = v)
    (w : W) (x : T) (h : (vec w).val.length < Usize.max) :
    ⦃ ⌜ True ⌝ ⦄ (do let v ← alloc.vec.Vec.push (vec w) x; ok (mk v) : RustM W)
    ⦃ ⇓ r => ⌜ (vec r).val = (vec w).val ++ [x] ⌝ ⦄ := by
  have := alloc.vec.Vec.push_spec (vec w) x h
  mvcgen [this]
  simp_all

noncomputable def body (push : W → T → RustM W) (msg : Str) (inst : DeserializeBytes T) (length : Std.Usize)
    (result : W) (remainder : Slice Std.U8) (read : Std.Usize) :
    RustM (ControlFlow (W × Slice Std.U8 × Std.Usize)
      (W × Slice Std.U8 × Std.Usize × core.option.Option Error)) := do
  if read < length
  then
    let r ← inst.tls_deserialize_bytes remainder
    match r with
    | core.result.Result.Ok p =>
      let (element, next_remainder) := p
      let i ← core.slice.Slice.len remainder
      let i1 ← core.slice.Slice.len next_remainder
      let consumed ← i - i1
      let result1 ← push result element
      if consumed = 0#usize
      then
        let a ← core.fmt.Arguments.from_str msg
        let s ← alloc.fmt.format a
        let s1 ← core.hint.must_use s
        ok (done (result1, next_remainder, read, core.option.Option.Some
          (Error.DecodingError s1)))
      else
        let read1 ← read + consumed
        ok (cont (result1, next_remainder, read1))
    | core.result.Result.Err e =>
      ok (done (result, remainder, read, core.option.Option.Some e))
  else ok (done (result, remainder, read, core.option.Option.None))

theorem body_char (vec : W → alloc.vec.Vec T) (push : W → T → RustM W)
    (push_spec : ∀ w x, (vec w).val.length < Usize.max →
      ⦃ ⌜ True ⌝ ⦄ push w x ⦃ ⇓ r => ⌜ (vec r).val = (vec w).val ++ [x] ⌝ ⦄)
    (msg : Str) (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (a0 : Std.Usize) (length : Std.Usize) (N : Nat)
    (hN : N ≤ Usize.max)
    (result : W) (remainder : Slice Std.U8) (read : Std.Usize)
    (hinv : DesLoopInv inst.SizeInst a0 N (vec result).val remainder read) :
    ⦃ ⌜ True ⌝ ⦄
    body push msg inst length result remainder read
    ⦃ ⇓ r => ⌜ match r with
      | .done (res, rem, _, fl) => fl = core.option.Option.None →
          ∃ s, SizeFoldRel inst.SizeInst a0 (vec res).val s ∧ s.val + rem.val.length = N
      | .cont (res, rem, rd) => DesLoopInv inst.SizeInst a0 N (vec res).val rem rd ∧
          rem.val.length < remainder.val.length ⌝ ⦄ := by
  have hd := fun b => hlaw.tls_deserialize_bytes_spec b (pre_holds_of_ok_true rfl)
  obtain ⟨hres, ⟨s, hs, hsN⟩, hr⟩ := hinv
  mvcgen [body, hd, push_spec, core.fmt.Arguments.from_str]
  case vc1.a =>
    rename_i hlt r p hx hpost r2 h2 r1 h1 r0 ha hb
    scalar_tac
  case vc3.hQ =>
    rename_i hlt r p hx hpost r2 h2 r1 h1 r0 ha hb res hnz hpush rd hrd
    obtain ⟨e, nxt⟩ := p
    obtain ⟨n, hn, hl⟩ := DeserializeBytes.post_ok_elim _ _ _ _ _ hpost
    subst h2 h1
    have l1 := Slice.len_val remainder
    have l2 := Slice.len_val nxt
    simp only [Slice.length] at l1 l2
    have hnz' : r0.val ≠ 0 := fun h => hnz (UScalar.eq_of_val_eq (by simpa using h))
    have hr0 : r0.val = n.val := by dsimp only at *; omega
    have hsn : (lenAddVal s n).val = s.val + n.val := lenAddVal_val s n (by dsimp only at *; omega)
    refine ⟨⟨?_, ⟨lenAddVal s n, ?_, ?_⟩, ?_⟩, ?_⟩
    · rw [hpush]; simp; dsimp only at *; omega
    · rw [hpush]; exact hs.snoc e n hn
    · dsimp only at *; omega
    · dsimp only at *; omega
    · dsimp only at *; omega
  case vc4.h_fail =>
    exfalso
    rename_i hlt r p hx hpost r2 h2 r1 h1 r0 ha hb res hnz hpush hbig
    obtain ⟨e, nxt⟩ := p
    obtain ⟨n, hn, hl⟩ := DeserializeBytes.post_ok_elim _ _ _ _ _ hpost
    subst h2 h1
    have l1 := Slice.len_val remainder
    have l2 := Slice.len_val nxt
    simp only [Slice.length] at l1 l2
    dsimp only at *
    scalar_tac
  case vc5.h_fail =>
    exfalso
    rename_i hlt r p hx hpost r2 h2 r1 h1 hlt2
    obtain ⟨e, nxt⟩ := p
    obtain ⟨n, hn, hl⟩ := DeserializeBytes.post_ok_elim _ _ _ _ _ hpost
    subst h2 h1
    have l1 := Slice.len_val remainder
    have l2 := Slice.len_val nxt
    simp only [Slice.length] at l1 l2
    dsimp only at *
    scalar_tac
  all_goals (try (intros; simp_all; done))
  exact ⟨s, hs, hsN⟩


/-- The loop of `deserialize_bytes`, over its body `bodyF` (fixed `length`). -/
def dloop (bodyF : W → Slice Std.U8 → Std.Usize → RustM (ControlFlow (W × Slice Std.U8 × Std.Usize)
      (W × Slice Std.U8 × Std.Usize × core.option.Option Error)))
    (result : W) (remainder : Slice Std.U8) (read : Std.Usize) :
    RustM (W × Slice Std.U8 × Std.Usize × core.option.Option Error) :=
  loop (fun (result1, remainder1, read1) => bodyF result1 remainder1 read1) (result, remainder, read)

theorem loop_char (vec : W → alloc.vec.Vec T) (push : W → T → RustM W)
    (push_spec : ∀ w x, (vec w).val.length < Usize.max →
      ⦃ ⌜ True ⌝ ⦄ push w x ⦃ ⇓ r => ⌜ (vec r).val = (vec w).val ++ [x] ⌝ ⦄)
    (inst : DeserializeBytes T) (length : Std.Usize) (msg : Str)
    {bodyF : W → Slice Std.U8 → Std.Usize → RustM (ControlFlow (W × Slice Std.U8 × Std.Usize)
      (W × Slice Std.U8 × Std.Usize × core.option.Option Error))}
    (hbody : bodyF = body push msg inst length)
    (hlaw : DeserializeBytes.Lawful T inst) (a0 : Std.Usize) (N : Nat) (hN : N ≤ Usize.max)
    (result : W) (remainder : Slice Std.U8) (read : Std.Usize)
    (hinv : DesLoopInv inst.SizeInst a0 N (vec result).val remainder read) :
    ⦃ ⌜ True ⌝ ⦄
    dloop bodyF result remainder read
    ⦃ ⇓ r => ⌜ r.2.2.2 = core.option.Option.None →
        ∃ s, SizeFoldRel inst.SizeInst a0 (vec r.1).val s ∧ s.val + r.2.1.val.length = N ⌝ ⦄ := by
  subst hbody
  unfold dloop
  apply Aeneas.Std.WP.spec_to_mvcgen
  apply Aeneas.Std.loop.spec_decr_nat
    (fun p : W × Slice Std.U8 × Std.Usize => p.2.1.val.length)
    (fun p => DesLoopInv inst.SizeInst a0 N (vec p.1).val p.2.1 p.2.2)
  · rintro ⟨res, rem, rd⟩ h
    obtain ⟨v, hv, hP⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp
      (body_char vec push push_spec msg inst hlaw a0 length N hN res rem rd h)
    dsimp only
    rw [hv]
    refine (Aeneas.Std.WP.spec_ok v).mpr ?_
    cases v with
    | done y => exact hP
    | cont x => exact hP
  · exact hinv


/-- `tls_serialized_length` of a `TlsVecU*` / `SecretTlsVecU*` / `TlsSliceU*`: fold of the closure `F`
over the elements (`asSlice`) from the prefix width `w`. -/
def serLen {X C : Type} (asSlice : X → RustM (Slice T))
    (F : core.ops.function.FnMut C (Std.Usize × T) Std.Usize) (c : C) (w : Std.Usize) (x : X) :
    RustM Std.Usize := do
  let s ← asSlice x
  let i ← core.slice.Slice.iter s
  core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold F i w c

theorem ok_view (x : Slice T) : ⦃ ⌜ True ⌝ ⦄ (ok x : RustM (Slice T)) ⦃ ⇓ s => ⌜ s = x ⌝ ⦄ := by
  mvcgen

theorem serLen_rel {X C : Type} (S : Size T) (hl : Size.Lawful T S)
    (asSlice : X → RustM (Slice T)) {view : X → Slice T}
    (has : ∀ x, ⦃ ⌜ True ⌝ ⦄ asSlice x ⦃ ⇓ s => ⌜ s = view x ⌝ ⦄)
    (F : core.ops.function.FnMut C (Std.Usize × T) Std.Usize)
    (hF : ∀ c a e, F.call_mut c (a, e) = (do
      let i ← S.tls_serialized_len e
      let i1 ← len_add a i
      ok (i1, c)))
    (c : C) (w : Std.Usize) (x : X) :
    ⦃ ⌜ True ⌝ ⦄ serLen asSlice F c w x ⦃ ⇓ r => ⌜ SizeFoldRel S w (view x).val r ⌝ ⦄ := by
  have hcall : ∀ c a e n, S.tls_serialized_len e = ok n → F.call_mut c (a, e) = ok (lenAddVal a n, c) := by
    intro c a e n hn
    simp [hF, hn, len_add_ok]
  have hf := size_fold_rel S (Size.lawful_ok S hl) _ hcall
  mvcgen [serLen, has, hf]
  intro h; subst_vars; exact h


/-- `deserialize_bytes` of a vector wrapper: length prefix `readLen`, conversion `conv` (unwrapped
with `dbg`), then the element loop `dloop` (`pieces`: the mismatch message literal). -/
noncomputable def deser {P E : Type} {M : Std.Usize} (mk : alloc.vec.Vec T → W)
    (readLen : Slice Std.U8 → RustM (core.result.Result (P × Slice Std.U8) Error))
    (conv : P → RustM (core.result.Result Std.Usize E)) (dbg : core.fmt.Debug E)
    (dloop : W → Slice Std.U8 → Std.Usize → Std.Usize →
      RustM (W × Slice Std.U8 × Std.Usize × core.option.Option Error))
    (pieces : Aeneas.Std.Array Std.U8 M) (bytes : Slice Std.U8) :
    RustM (core.result.Result (W × Slice Std.U8) Error) := do
  let v ← alloc.vec.Vec.new T
  let r ← readLen bytes
  let cf ← core.result.Result.Insts.CoreOpsTry_traitTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue p =>
    let (len, remainder) := p
    let r1 ← conv len
    let length ← core.result.Result.unwrap dbg r1
    let (result, remainder1, read, failure) ← dloop (mk v) remainder length 0#usize
    match failure with
    | core.option.Option.None =>
      if read != length
      then
        let a ← core.fmt.rt.Argument.new_display core.Usize.Insts.CoreFmtDisplay length
        let a1 ← core.fmt.rt.Argument.new_display core.Usize.Insts.CoreFmtDisplay read
        let a2 ← core.fmt.Arguments.new pieces (Array.make 2#usize [ a, a1 ])
        let s ← alloc.fmt.format a2
        let s1 ← core.hint.must_use s
        ok (core.result.Result.Err (Error.DecodingError s1))
      else ok (core.result.Result.Ok (result, remainder1))
    | core.option.Option.Some e => ok (core.result.Result.Err e)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
      (W × Slice Std.U8) (core.convert.From.Blanket Error) residual


/-- Post of the element loop from the prefix width `w` and the input length `N`. -/
abbrev LoopPost (S : Size T) (vec : W → alloc.vec.Vec T) (w : Std.Usize) (N : Nat)
    (r : W × Slice Std.U8 × Std.Usize × core.option.Option Error) : Prop :=
  r.2.2.2 = core.option.Option.None → ∃ s, SizeFoldRel S w (vec r.1).val s ∧ s.val + r.2.1.val.length = N

theorem deser_char {P E : Type} {M : Std.Usize} (S : Size T) (vec : W → alloc.vec.Vec T)
    (mk : alloc.vec.Vec T → W) (hmk : ∀ v, vec (mk v) = v) (size : W → RustM Std.Usize)
    (w : Std.Usize) (hsz : ∀ v, ⦃ ⌜ True ⌝ ⦄ size v ⦃ ⇓ r => ⌜ SizeFoldRel S w (vec v).val r ⌝ ⦄)
    (readLen : Slice Std.U8 → RustM (core.result.Result (P × Slice Std.U8) Error))
    (hread : ∀ bytes, ⦃ ⌜ True ⌝ ⦄ readLen bytes
      ⦃ ⇓ r => ⌜ ∀ p, r = .Ok p → p.2.val.length + w.val = bytes.val.length ⌝ ⦄)
    (conv : P → RustM (core.result.Result Std.Usize E))
    (hconv : ∀ p, ⦃ ⌜ True ⌝ ⦄ conv p ⦃ ⇓ r => ⌜ ∃ y, r = .Ok y ⌝ ⦄) (dbg : core.fmt.Debug E)
    (dloop : W → Slice Std.U8 → Std.Usize → Std.Usize →
      RustM (W × Slice Std.U8 × Std.Usize × core.option.Option Error))
    (hloop : ∀ N, N ≤ Usize.max → ∀ result remainder length read,
      DesLoopInv S w N (vec result).val remainder read →
      ⦃ ⌜ True ⌝ ⦄ dloop result remainder length read ⦃ ⇓ r => ⌜ LoopPost S vec w N r ⌝ ⦄)
    (pieces : Aeneas.Std.Array Std.U8 M) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ deser mk readLen conv dbg dloop pieces bytes
    ⦃ ⇓ r => ⌜ ∀ v rem, r = .Ok (v, rem) → ∃ n, size v = ok n ∧
        rem.val.length + n.val = bytes.val.length ⌝ ⦄ := by
  have hN : bytes.val.length ≤ Usize.max := by have := bytes.property; scalar_tac
  have hl := hloop _ hN
  mvcgen [deser, hread, hconv, hl, core.result.Result.unwrap]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  all_goals (try (intro _ _ h; cases h; done))
  all_goals (try (intros; simp [PostCond.ok]; done))
  all_goals (try (exfalso; simp_all; done))
  case vc1.a =>
    subst_vars
    simp only [core.result.Result.Ok.injEq, forall_eq'] at *
    refine ⟨by simp [hmk, Slice.new], ⟨w, by rw [hmk]; exact .nil _, ?_⟩, ?_⟩ <;> scalar_tac
  case vc3 =>
    intro v rem h
    simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨s, hs, hsN⟩ := ‹LoopPost _ _ _ _ _› ‹_ = core.option.Option.None›
    obtain ⟨n, hn, hP⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp (hsz _)
    exact ⟨n, hn, (hs.functional hP) ▸ (Nat.add_comm _ _).trans hsN⟩


/-- The function-level post of `deserialize_bytes` (`ensures` closure: `rem.len + size v = bytes.len`). -/
def post (size : W → RustM Std.Usize) (bytes : Slice Std.U8)
    (res : core.result.Result (W × Slice Std.U8) Error) : RustM Bool := do
  let b ← core.result.Result.is_err res
  if b
  then ok true
  else
    core.result.Result.is_ok_and
      ({ call_once := fun (c : Slice Std.U8) (tupled_args : W × Slice Std.U8) => do
          let (vec, remainder) := tupled_args
          let i ← core.slice.Slice.len remainder
          let i1 ← size vec
          let i2 ← i + i1
          let i3 ← core.slice.Slice.len c
          ok (i2 = i3) } : core.ops.function.FnOnce (Slice Std.U8) (W × Slice Std.U8) Bool) res bytes

theorem post_of_char (size : W → RustM Std.Usize) (bytes : Slice Std.U8)
    (r : core.result.Result (W × Slice Std.U8) Error)
    (h : ∀ v rem, r = .Ok (v, rem) → ∃ n, size v = ok n ∧ rem.val.length + n.val = bytes.val.length) :
    (post size bytes r).holds := by
  have hl : ∀ (s : Slice Std.U8), core.slice.Slice.len s = ok (Slice.len s) := by
    intro s; unfold core.slice.Slice.len; rfl
  cases r with
  | Err e =>
    simp [post, core.result.Result.is_err, RustM.holds]
    mvcgen
  | Ok p =>
    obtain ⟨v, rem⟩ := p
    obtain ⟨n, hn, hrem⟩ := h v rem rfl
    have hb : bytes.val.length ≤ Std.Usize.max := by
      have := bytes.property; scalar_tac
    have hadd : (Slice.len rem + n : RustM Std.Usize) = ok (Slice.len bytes) := by
      have := Aeneas.Std.UScalar.add_equiv (Slice.len rem) n
      cases hc : (Slice.len rem + n : RustM Std.Usize) with
      | ok z =>
        rw [hc] at this
        obtain ⟨_, hz, _⟩ := this
        congr 1
        apply UScalar.eq_of_val_eq
        simp only [Slice.len_val, Slice.length] at hz ⊢
        omega
      | fail e =>
        rw [hc] at this
        exfalso
        apply this.2
        simp only [Slice.len_val, Slice.length] at *
        scalar_tac
      | div => rw [hc] at this; exact this.elim
    simp only [post, core.result.Result.is_err, core.result.Result.is_ok_and, hl]
    simp [hn, hadd, RustM.holds]
    mvcgen

/-- The function-level post from a total characterization. -/
theorem fc_of_char (size : W → RustM Std.Usize) (bytes : Slice Std.U8)
    {m : RustM (core.result.Result (W × Slice Std.U8) Error)}
    (h : ⦃ ⌜ True ⌝ ⦄ m ⦃ ⇓ r => ⌜ ∀ v rem, r = .Ok (v, rem) → ∃ n, size v = ok n ∧
      rem.val.length + n.val = bytes.val.length ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄ m ⦃ ⇓? res => ⌜ (post size bytes res).holds ⌝ ⦄ := by
  obtain ⟨v, hv, hP⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp h
  rw [hv]
  apply RustM.ok_spec
  exact post_of_char size bytes v hP

/-- The function-level post from a partial characterization. -/
theorem fc_of_char_partial (size : W → RustM Std.Usize) (bytes : Slice Std.U8)
    {m : RustM (core.result.Result (W × Slice Std.U8) Error)}
    (h : ⦃ ⌜ True ⌝ ⦄ m ⦃ ⇓? r => ⌜ ∀ v rem, r = .Ok (v, rem) → ∃ n, size v = ok n ∧
      rem.val.length + n.val = bytes.val.length ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄ m ⦃ ⇓? res => ⌜ (post size bytes res).holds ⌝ ⦄ :=
  partial_triple_of_ok fun r hr => post_of_char size bytes r (ok_of_partial_triple h hr)


/-- The remainder after a successful length-prefix read of width `w = n` (from `U*_deserialize_char`). -/
theorem prefix_len {U X : Type} (w : Std.Usize) (n : Nat) (hn : w.val = n) {f : X → U} {A : Slice Std.U8 → X → Prop}
    {readLen : Slice Std.U8 → RustM (core.result.Result (U × Slice Std.U8) Error)}
    (h : ∀ bytes, ⦃ ⌜ True ⌝ ⦄ readLen bytes
      ⦃ ⇓ r => ⌜ (n ≤ bytes.val.length → ∃ (a : X) (t : Slice Std.U8),
          A bytes a ∧ t.val = bytes.val.drop n ∧ r = .Ok (f a, t)) ∧
        (bytes.val.length < n → r = .Err Error.EndOfStream) ⌝ ⦄)
    (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ readLen bytes
    ⦃ ⇓ r => ⌜ ∀ p, r = .Ok p → p.2.val.length + w.val = bytes.val.length ⌝ ⦄ := by
  obtain ⟨r, hr, hP⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp (h bytes)
  rw [hr, hn]
  apply RustM.ok_spec
  exact fun p hp => prefix_rem n ⟨fun h => let ⟨_, t, _, ht, hr⟩ := hP.1 h; ⟨t, ht, _, hr⟩, hP.2⟩ hp

/-- A conversion that always returns `Ok`. -/
theorem conv_ok {P E : Type} {conv : P → RustM (core.result.Result Std.Usize E)} {g : P → Std.Usize}
    (h : ∀ p, ⦃ ⌜ True ⌝ ⦄ conv p ⦃ ⇓ r => ⌜ r = .Ok (g p) ⌝ ⦄) (p : P) :
    ⦃ ⌜ True ⌝ ⦄ conv p ⦃ ⇓ r => ⌜ ∃ y, r = .Ok y ⌝ ⦄ := by
  obtain ⟨r, hr, hP⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp (h p)
  rw [hr]
  apply RustM.ok_spec
  exact ⟨_, hP⟩

end TlsVecGen

/-! #### `TlsSliceU*::tls_serialized_length` -/

/-- `TlsSliceU8::tls_serialized_length` does not fail when the element size does not. -/
theorem tls_vec.TlsSliceU8.tls_serialized_length_pf {T : Type} (SizeInst : Size T)
    (SizeInstLawful : Size.Lawful T SizeInst) (self_ : tls_vec.TlsSliceU8 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsSliceU8.tls_serialized_length SizeInst self_
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  pf_of_total (TlsVecGen.serLen_rel SizeInst SizeInstLawful tls_vec.TlsSliceU8.as_slice TlsVecGen.ok_view _ (fun _ _ _ => rfl) () 1#usize self_)

/-- `TlsSliceU16::tls_serialized_length` does not fail when the element size does not. -/
theorem tls_vec.TlsSliceU16.tls_serialized_length_pf {T : Type} (SizeInst : Size T)
    (SizeInstLawful : Size.Lawful T SizeInst) (self_ : tls_vec.TlsSliceU16 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsSliceU16.tls_serialized_length SizeInst self_
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  pf_of_total (TlsVecGen.serLen_rel SizeInst SizeInstLawful tls_vec.TlsSliceU16.as_slice TlsVecGen.ok_view _ (fun _ _ _ => rfl) () 2#usize self_)

/-- `TlsSliceU24::tls_serialized_length` does not fail when the element size does not. -/
theorem tls_vec.TlsSliceU24.tls_serialized_length_pf {T : Type} (SizeInst : Size T)
    (SizeInstLawful : Size.Lawful T SizeInst) (self_ : tls_vec.TlsSliceU24 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsSliceU24.tls_serialized_length SizeInst self_
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  pf_of_total (TlsVecGen.serLen_rel SizeInst SizeInstLawful tls_vec.TlsSliceU24.as_slice TlsVecGen.ok_view _ (fun _ _ _ => rfl) () 3#usize self_)

/-- `TlsSliceU32::tls_serialized_length` does not fail when the element size does not. -/
theorem tls_vec.TlsSliceU32.tls_serialized_length_pf {T : Type} (SizeInst : Size T)
    (SizeInstLawful : Size.Lawful T SizeInst) (self_ : tls_vec.TlsSliceU32 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsSliceU32.tls_serialized_length SizeInst self_
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  pf_of_total (TlsVecGen.serLen_rel SizeInst SizeInstLawful tls_vec.TlsSliceU32.as_slice TlsVecGen.ok_view _ (fun _ _ _ => rfl) () 4#usize self_)

/-! ### Generic `TlsByteVecU*::deserialize_bytes_bytes` (`TlsByteVecGen`)

As `TlsVecGen`: the per-width functions are one generic function (`TlsByteVecGen.deser`) up to the
wrapper, the prefix codec / conversion and the width, linked by `rfl` after a case split on the first
`?` match. `content` (partial) and `pf` are proved once; per width `deserialize_content` combines
them, and `deserialize_char(_le)` follow from it by `Content.len`. -/

namespace TlsByteVecGen

variable {W : Type}

/-- `TlsByteVecU*::deserialize_bytes_bytes` over an abstract wrapper (`mk`), length prefix `readLen`
of width `w`, and its conversion `conv` to `usize` (unwrapped with `dbg`). -/
def deser {P E : Type} (mk : alloc.vec.Vec Std.U8 → W)
    (readLen : Slice Std.U8 → RustM (core.result.Result (P × Slice Std.U8) Error))
    (conv : P → RustM (core.result.Result Std.Usize E)) (dbg : core.fmt.Debug E) (w : Std.Usize)
    (bytes : Slice Std.U8) : RustM (core.result.Result (W × Slice Std.U8) Error) := do
  let r ← readLen bytes
  let cf ← core.result.Result.Insts.CoreOpsTry_traitTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue p =>
    let (type_len, remainder) := p
    let r1 ← conv type_len
    let len ← core.result.Result.unwrap dbg r1
    let o ← core.num.Usize.checked_add len w
    let r2 ← core.option.Option.ok_or o Error.InvalidVectorLength
    let cf1 ← core.result.Result.Insts.CoreOpsTry_traitTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let o1 ←
        core.slice.Slice.get
          (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
          Std.U8) bytes { start := w, «end» := val }
      let r3 ← core.option.Option.ok_or o1 Error.EndOfStream
      let cf2 ← core.result.Result.Insts.CoreOpsTry_traitTry.branch r3
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let v ← alloc.slice.Slice.to_vec core.U8.Insts.CoreCloneClone val1
        let o2 ←
          core.slice.Slice.get
            (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
            Std.U8) remainder { start := len }
        let r4 ← core.option.Option.ok_or o2 Error.EndOfStream
        let cf3 ← core.result.Result.Insts.CoreOpsTry_traitTry.branch r4
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          ok (core.result.Result.Ok (mk v, val2))
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
            (W × Slice Std.U8) (core.convert.From.Blanket Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
          (W × Slice Std.U8) (core.convert.From.Blanket Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
        (W × Slice Std.U8) (core.convert.From.Blanket Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
      (W × Slice Std.U8) (core.convert.From.Blanket Error) residual


theorem content_rel {P E : Type} (vec : W → alloc.vec.Vec Std.U8) (mk : alloc.vec.Vec Std.U8 → W)
    (hmk : ∀ v, vec (mk v) = v) (enc : P → List Std.U8) (R : P → Nat → Prop) (w : Std.Usize)
    (henc : ∀ p, (enc p).length = w.val)
    (readLen : Slice Std.U8 → RustM (core.result.Result (P × Slice Std.U8) Error))
    (hread : ∀ bytes, ⦃ ⌜ True ⌝ ⦄ readLen bytes ⦃ ⇓ r => ⌜ ∀ p, r = .Ok p →
      bytes.val = enc p.1 ++ p.2.val ⌝ ⦄)
    (conv : P → RustM (core.result.Result Std.Usize E))
    (hconv : ∀ p, ⦃ ⌜ True ⌝ ⦄ conv p ⦃ ⇓? r => ⌜ ∃ y, r = .Ok y ∧ R p y.val ⌝ ⦄)
    (dbg : core.fmt.Debug E) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ deser mk readLen conv dbg w bytes
    ⦃ ⇓? r => ⌜ ∀ v t, r = .Ok (v, t) → ∃ p : P, R p (vec v).val.length ∧
        bytes.val = enc p ++ ((vec v).val ++ t.val) ⌝ ⦄ := by
  mvcgen [-core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_some_spec,
    deser, hread, hconv, core.option.Option.ok_or_spec,
    core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_content_spec]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  all_goals (try (intros; simp [PostCond.ok]; done))
  case vc1.h => obtain ⟨y, hy, -⟩ := ‹∃ y, _ ∧ _›; exact ⟨y, hy⟩
  case vc2 =>
    rename_i r0 hP r1 p _ r2 hc len hlen o hca r3 hr3 _ val _ o1 hget1 r5 hr5 _ val1 _ v0 hv0 o2 hget2
      r6 hr6 _ val2 _ e0 e1 e2 e3
    rintro v t ⟨⟩
    have hb := hP p e0
    have hw := henc p.1
    obtain ⟨y, rfl, hyv⟩ := hc
    cases hlen
    have h1 := hget1 val1 (ok_or_eq_ok hr5 e2)
    have ho := ok_or_eq_ok hr3 e1
    have h2 : val.val = len.val + w.val := by
      by_cases hov : len.val + w.val ≤ Usize.max
      · obtain ⟨z, hz, hzv⟩ := hca.1 hov
        rw [hz] at ho; cases ho; exact hzv
      · rw [hca.2 (by omega)] at ho; cases ho
    have ho2 := ok_or_eq_ok hr6 e3
    have hle : len.val ≤ p.2.val.length := by
      by_contra hn; rw [hget2.2 (by omega)] at ho2; cases ho2
    obtain ⟨t2, ht2, ht2'⟩ := hget2.1 hle
    rw [ht2] at ho2; cases ho2
    have hd : bytes.val.drop w.val = p.2.val := by rw [hb, ← hw, List.drop_left]
    have hv : (vec (mk v0)).val = p.2.val.take len.val := by
      rw [hmk, hv0, h1.2.2, hd, h2, Nat.add_sub_cancel]
    refine ⟨p.1, ?_, ?_⟩
    · rw [hv, List.length_take, Nat.min_eq_left hle]; exact hyv
    · rw [hv, ht2', List.take_append_drop]; exact hb

/-- `content_rel` with the prefix value `pval p` as the payload length. -/
theorem content {P E : Type} (vec : W → alloc.vec.Vec Std.U8) (mk : alloc.vec.Vec Std.U8 → W)
    (hmk : ∀ v, vec (mk v) = v) (enc : P → List Std.U8) (pval : P → Nat) (w : Std.Usize)
    (henc : ∀ p, (enc p).length = w.val)
    (readLen : Slice Std.U8 → RustM (core.result.Result (P × Slice Std.U8) Error))
    (hread : ∀ bytes, ⦃ ⌜ True ⌝ ⦄ readLen bytes ⦃ ⇓ r => ⌜ ∀ p, r = .Ok p →
      bytes.val = enc p.1 ++ p.2.val ⌝ ⦄)
    (conv : P → RustM (core.result.Result Std.Usize E))
    (hconv : ∀ p, ⦃ ⌜ True ⌝ ⦄ conv p ⦃ ⇓? r => ⌜ ∃ y, r = .Ok y ∧ y.val = pval p ⌝ ⦄)
    (dbg : core.fmt.Debug E) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ deser mk readLen conv dbg w bytes
    ⦃ ⇓? r => ⌜ ∀ v t, r = .Ok (v, t) → ∃ p : P, pval p = (vec v).val.length ∧
        bytes.val = enc p ++ ((vec v).val ++ t.val) ⌝ ⦄ := by
  have h := content_rel vec mk hmk enc (fun p n => n = pval p) w henc readLen hread conv hconv dbg bytes
  refine partial_triple_of_ok fun r hr v t hv => ?_
  obtain ⟨p, hp, hb⟩ := ok_of_partial_triple h hr v t hv
  exact ⟨p, hp.symm, hb⟩

theorem pf {P E : Type} (mk : alloc.vec.Vec Std.U8 → W) (w : Std.Usize)
    (readLen : Slice Std.U8 → RustM (core.result.Result (P × Slice Std.U8) Error))
    (hread : ∀ bytes, ⦃ ⌜ True ⌝ ⦄ readLen bytes ⦃ ⇓ _ => ⌜ True ⌝ ⦄)
    (conv : P → RustM (core.result.Result Std.Usize E))
    (hconv : ∀ p, ⦃ ⌜ True ⌝ ⦄ conv p ⦃ ⇓ r => ⌜ ∃ y, r = .Ok y ⌝ ⦄)
    (dbg : core.fmt.Debug E) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ deser mk readLen conv dbg w bytes ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  mvcgen [deser, hread, hconv, core.option.Option.ok_or_spec]
  try_vcs


/-- The post of `content`: the input is the encoded prefix, the payload, then the remainder. -/
abbrev Content {P : Type} (vec : W → alloc.vec.Vec Std.U8) (enc : P → List Std.U8) (pval : P → Nat)
    (bytes : Slice Std.U8) (r : core.result.Result (W × Slice Std.U8) Error) : Prop :=
  ∀ v t, r = .Ok (v, t) → ∃ p : P, pval p = (vec v).val.length ∧
    bytes.val = enc p ++ ((vec v).val ++ t.val)

theorem Content.len {P : Type} {vec : W → alloc.vec.Vec Std.U8} {enc : P → List Std.U8}
    {pval : P → Nat} {bytes : Slice Std.U8} {r : core.result.Result (W × Slice Std.U8) Error}
    (h : Content vec enc pval bytes r) (n : Nat) (henc : ∀ p, (enc p).length = n) (bound : Nat)
    (hb : ∀ p, pval p ≤ bound) :
    ∀ v t, r = .Ok (v, t) → t.val.length + n + (vec v).val.length = bytes.val.length ∧
      (vec v).val.length ≤ bound := by
  intro v t hr
  obtain ⟨p, hp, hb'⟩ := h v t hr
  have := congrArg List.length hb'
  simp only [List.length_append, henc] at this
  exact ⟨by omega, hp ▸ hb p⟩

/-- `bytes = enc x ++ rest` after a successful prefix read (from a `U*_deserialize_char`). -/
theorem prefix_split {U X : Type} (n : Nat) {f : X → U} {g : X → List Std.U8} (enc : U → List Std.U8)
    (hrt : ∀ a, enc (f a) = g a)
    {readLen : Slice Std.U8 → RustM (core.result.Result (U × Slice Std.U8) Error)}
    (h : ∀ bytes, ⦃ ⌜ True ⌝ ⦄ readLen bytes
      ⦃ ⇓ r => ⌜ (n ≤ bytes.val.length → ∃ (a : X) (t : Slice Std.U8),
          g a = bytes.val.take n ∧ t.val = bytes.val.drop n ∧ r = .Ok (f a, t)) ∧
        (bytes.val.length < n → r = .Err Error.EndOfStream) ⌝ ⦄)
    (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ readLen bytes ⦃ ⇓ r => ⌜ ∀ p, r = .Ok p → bytes.val = enc p.1 ++ p.2.val ⌝ ⦄ := by
  refine triple_post_mono (h bytes) fun r hP p hp => ?_
  by_cases hn : n ≤ bytes.val.length
  · obtain ⟨a, t, ha, ht, rfl⟩ := hP.1 hn
    cases hp
    rw [hrt, ha, ht, List.take_append_drop]
  · rw [hP.2 (by omega)] at hp; cases hp

/-- A conversion returning `Ok (g p)`, with `g p` of value `pval p`. -/
theorem conv_val {P E : Type} {conv : P → RustM (core.result.Result Std.Usize E)} {g : P → Std.Usize}
    (pval : P → Nat) (h : ∀ p, ⦃ ⌜ True ⌝ ⦄ conv p ⦃ ⇓ r => ⌜ r = .Ok (g p) ⌝ ⦄)
    (hg : ∀ p, (g p).val = pval p) (p : P) :
    ⦃ ⌜ True ⌝ ⦄ conv p ⦃ ⇓? r => ⌜ ∃ y, r = .Ok y ∧ y.val = pval p ⌝ ⦄ := by
  obtain ⟨r, hr, hP⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp (h p)
  refine partial_triple_of_ok fun r' hr' => ⟨g p, ?_, hg p⟩
  rw [hr] at hr'; cases hr'; exact hP

end TlsByteVecGen

/-! #### `TlsByteVecU16` -/

/-- `TlsByteVecU16::deserialize_bytes_bytes` is the generic one. -/
theorem tls_vec.TlsByteVecU16.deserialize_bytes_bytes_eq : tls_vec.TlsByteVecU16.deserialize_bytes_bytes =
    TlsByteVecGen.deser tls_vec.TlsByteVecU16.mk U16.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes
      (core.convert.TryFromTUInfallible.Blanket.try_from
        (core.convert.Into.Blanket core.Usize.Insts.CoreConvertFromU16))
      core.convert.Infallible.Insts.CoreFmtDebug 2#usize := by
  funext bytes
  unfold tls_vec.TlsByteVecU16.deserialize_bytes_bytes TlsByteVecGen.deser
  congr 1; funext r; congr 1; funext cf; cases cf <;> rfl

/-- `TlsByteVecU16::deserialize_bytes_bytes` never panics; on success the input is the 2-byte length prefix, the payload, then the remainder. -/
theorem tls_vec.TlsByteVecU16.deserialize_content (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU16.deserialize_bytes_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : tls_vec.TlsByteVecU16) (t : Slice Std.U8), r = .Ok (v, t) →
        ∃ n : Std.U16, n.val = v.vec.val.length ∧
          bytes.val = (Aeneas.Std.core.num.U16.to_be_bytes n).val ++ (v.vec.val ++ t.val) ⌝ ⦄ := by
  rw [tls_vec.TlsByteVecU16.deserialize_bytes_bytes_eq]
  have hread := TlsByteVecGen.prefix_split 2 (fun n : Std.U16 => (Aeneas.Std.core.num.U16.to_be_bytes n).val)
    (fun a => congrArg Subtype.val (U16_to_be_bytes_from_be_bytes a)) U16_deserialize_char
  exact total_of_pf_partial
    (TlsByteVecGen.pf _ _ _ (fun b => pf_of_total (hread b)) _
      (TlsVecGen.conv_ok core.convert.TryFromTUInfallible.Blanket.try_from_Usize_U16_spec) _ bytes)
    (TlsByteVecGen.content tls_vec.TlsByteVecU16.vec _ (fun _ => rfl) _ (fun n : Std.U16 => n.val) 2#usize
      (fun n => (Aeneas.Std.core.num.U16.to_be_bytes n).property) _ hread _
      (TlsByteVecGen.conv_val _ core.convert.TryFromTUInfallible.Blanket.try_from_Usize_U16_spec
        (fun _ => by simp)) _ bytes)

theorem tls_vec.TlsByteVecU16.deserialize_char_le (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU16.deserialize_bytes_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : tls_vec.TlsByteVecU16) (t : Slice Std.U8), r = .Ok (v, t) →
        t.val.length + 2 + v.vec.val.length = bytes.val.length ∧
          v.vec.val.length ≤ 65535 ⌝ ⦄ :=
  triple_post_mono (tls_vec.TlsByteVecU16.deserialize_content bytes) fun _ h =>
    TlsByteVecGen.Content.len (vec := tls_vec.TlsByteVecU16.vec) h 2 (fun n => by simp) 65535 (fun n => by scalar_tac)

theorem tls_vec.TlsByteVecU16.deserialize_char (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU16.deserialize_bytes_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : tls_vec.TlsByteVecU16) (t : Slice Std.U8), r = .Ok (v, t) →
        t.val.length + 2 + v.vec.val.length = bytes.val.length ⌝ ⦄ :=
  triple_post_mono (tls_vec.TlsByteVecU16.deserialize_char_le bytes) fun _ h v t hr => (h v t hr).1

/-! #### `TlsByteVecU8` -/

/-- `TlsByteVecU8::deserialize_bytes_bytes` is the generic one. -/
theorem tls_vec.TlsByteVecU8.deserialize_bytes_bytes_eq : tls_vec.TlsByteVecU8.deserialize_bytes_bytes =
    TlsByteVecGen.deser tls_vec.TlsByteVecU8.mk U8.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes
      (core.convert.TryFromTUInfallible.Blanket.try_from
        (core.convert.Into.Blanket core.Usize.Insts.CoreConvertFromU8))
      core.convert.Infallible.Insts.CoreFmtDebug 1#usize := by
  funext bytes
  unfold tls_vec.TlsByteVecU8.deserialize_bytes_bytes TlsByteVecGen.deser
  congr 1; funext r; congr 1; funext cf; cases cf <;> rfl

/-- `TlsByteVecU8::deserialize_bytes_bytes` never panics; on success the input is the 1-byte length prefix, the payload, then the remainder. -/
theorem tls_vec.TlsByteVecU8.deserialize_content (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU8.deserialize_bytes_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : tls_vec.TlsByteVecU8) (t : Slice Std.U8), r = .Ok (v, t) →
        ∃ n : Std.U8, n.val = v.vec.val.length ∧ bytes.val = n :: (v.vec.val ++ t.val) ⌝ ⦄ := by
  rw [tls_vec.TlsByteVecU8.deserialize_bytes_bytes_eq]
  have hread := TlsByteVecGen.prefix_split 1 (fun n : Std.U8 => [n])
    (fun a => by
      have := congrArg Subtype.val (U8_to_be_bytes_from_be_bytes a)
      rwa [U8_to_be_bytes_val] at this) U8_deserialize_char
  exact total_of_pf_partial
    (TlsByteVecGen.pf _ _ _ (fun b => pf_of_total (hread b)) _
      (TlsVecGen.conv_ok core.convert.TryFromTUInfallible.Blanket.try_from_Usize_U8_spec) _ bytes)
    (TlsByteVecGen.content tls_vec.TlsByteVecU8.vec _ (fun _ => rfl) (fun n : Std.U8 => [n]) (fun n : Std.U8 => n.val) 1#usize
      (fun n => rfl) _ hread _
      (TlsByteVecGen.conv_val _ core.convert.TryFromTUInfallible.Blanket.try_from_Usize_U8_spec
        (fun _ => by simp)) _ bytes)

theorem tls_vec.TlsByteVecU8.deserialize_char_le (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU8.deserialize_bytes_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : tls_vec.TlsByteVecU8) (t : Slice Std.U8), r = .Ok (v, t) →
        t.val.length + 1 + v.vec.val.length = bytes.val.length ∧
          v.vec.val.length ≤ 255 ⌝ ⦄ :=
  triple_post_mono (tls_vec.TlsByteVecU8.deserialize_content bytes) fun _ h =>
    TlsByteVecGen.Content.len (vec := tls_vec.TlsByteVecU8.vec) (enc := fun n : Std.U8 => [n]) (pval := fun n => n.val)
      (fun v t hr => h v t hr) 1 (fun n => rfl) 255 (fun n => by scalar_tac)

theorem tls_vec.TlsByteVecU8.deserialize_char (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU8.deserialize_bytes_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : tls_vec.TlsByteVecU8) (t : Slice Std.U8), r = .Ok (v, t) →
        t.val.length + 1 + v.vec.val.length = bytes.val.length ⌝ ⦄ :=
  triple_post_mono (tls_vec.TlsByteVecU8.deserialize_char_le bytes) fun _ h v t hr => (h v t hr).1

/-! #### `TlsByteVecU32` -/

/-- `TlsByteVecU32::deserialize_bytes_bytes` is the generic one. -/
theorem tls_vec.TlsByteVecU32.deserialize_bytes_bytes_eq : tls_vec.TlsByteVecU32.deserialize_bytes_bytes =
    TlsByteVecGen.deser tls_vec.TlsByteVecU32.mk U32.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes
      core.Usize.Insts.CoreConvertTryFromU32TryFromIntError.try_from
      core.num.error.TryFromIntError.Insts.CoreFmtDebug 4#usize := by
  funext bytes
  unfold tls_vec.TlsByteVecU32.deserialize_bytes_bytes TlsByteVecGen.deser
  congr 1; funext r; congr 1; funext cf; cases cf <;> rfl

/-- `TlsByteVecU32::deserialize_bytes_bytes` never panics; on success the input is the 4-byte length prefix, the payload, then the remainder. -/
theorem tls_vec.TlsByteVecU32.deserialize_content (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU32.deserialize_bytes_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : tls_vec.TlsByteVecU32) (t : Slice Std.U8), r = .Ok (v, t) →
        ∃ n : Std.U32, n.val = v.vec.val.length ∧
          bytes.val = (Aeneas.Std.core.num.U32.to_be_bytes n).val ++ (v.vec.val ++ t.val) ⌝ ⦄ := by
  rw [tls_vec.TlsByteVecU32.deserialize_bytes_bytes_eq]
  have hread := TlsByteVecGen.prefix_split 4 (fun n : Std.U32 => (Aeneas.Std.core.num.U32.to_be_bytes n).val)
    (fun a => congrArg Subtype.val (U32_to_be_bytes_from_be_bytes a)) U32_deserialize_char
  exact total_of_pf_partial
    (TlsByteVecGen.pf _ _ _ (fun b => pf_of_total (hread b)) _
      (TlsVecGen.conv_ok core.Usize.Insts.CoreConvertTryFromU32TryFromIntError.try_from_spec) _ bytes)
    (TlsByteVecGen.content tls_vec.TlsByteVecU32.vec _ (fun _ => rfl) _ (fun n : Std.U32 => n.val) 4#usize
      (fun n => (Aeneas.Std.core.num.U32.to_be_bytes n).property) _ hread _
      (TlsByteVecGen.conv_val _ core.Usize.Insts.CoreConvertTryFromU32TryFromIntError.try_from_spec
        (fun _ => by simp)) _ bytes)

theorem tls_vec.TlsByteVecU32.deserialize_char_le (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU32.deserialize_bytes_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : tls_vec.TlsByteVecU32) (t : Slice Std.U8), r = .Ok (v, t) →
        t.val.length + 4 + v.vec.val.length = bytes.val.length ∧
          v.vec.val.length ≤ 4294967295 ⌝ ⦄ :=
  triple_post_mono (tls_vec.TlsByteVecU32.deserialize_content bytes) fun _ h =>
    TlsByteVecGen.Content.len (vec := tls_vec.TlsByteVecU32.vec) h 4 (fun n => by simp) 4294967295 (fun n => by scalar_tac)

theorem tls_vec.TlsByteVecU32.deserialize_char (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU32.deserialize_bytes_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : tls_vec.TlsByteVecU32) (t : Slice Std.U8), r = .Ok (v, t) →
        t.val.length + 4 + v.vec.val.length = bytes.val.length ⌝ ⦄ :=
  triple_post_mono (tls_vec.TlsByteVecU32.deserialize_char_le bytes) fun _ h v t hr => (h v t hr).1

/-! #### `TlsByteVecU24` -/

/-- `TlsByteVecU24::deserialize_bytes_bytes` is the generic one. -/
theorem tls_vec.TlsByteVecU24.deserialize_bytes_bytes_eq : tls_vec.TlsByteVecU24.deserialize_bytes_bytes =
    TlsByteVecGen.deser tls_vec.TlsByteVecU24.mk U24.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes
      (core.convert.TryFromTUInfallible.Blanket.try_from
        (core.convert.Into.Blanket Usize.Insts.CoreConvertFromU24))
      core.convert.Infallible.Insts.CoreFmtDebug 3#usize := by
  funext bytes
  unfold tls_vec.TlsByteVecU24.deserialize_bytes_bytes TlsByteVecGen.deser
  congr 1; funext r; congr 1; funext cf; cases cf <;> rfl

/-- The big-endian value of a 3-byte prefix. -/
def U24.pval (a : Aeneas.Std.Array Std.U8 3#usize) : Nat :=
  a.val[0]!.val * 65536 + a.val[1]!.val * 256 + a.val[2]!.val

/-- `usize::try_from(U24)` (blanket `Into` impl) never fails: it is `Ok` of `U24.pval`. -/
theorem core.convert.TryFromTUInfallible.Blanket.try_from_Usize_U24_val (x : Aeneas.Std.Array Std.U8 3#usize) :
    ⦃ ⌜ True ⌝ ⦄
    core.convert.TryFromTUInfallible.Blanket.try_from
      (core.convert.Into.Blanket Usize.Insts.CoreConvertFromU24) x
    ⦃ ⇓ r => ⌜ ∃ y, r = .Ok y ∧ y.val = U24.pval x ⌝ ⦄ :=
  triple_post_mono (core.convert.TryFromTUInfallible.Blanket.try_from_Usize_U24_content x)
    fun _ ⟨y, hy, hh⟩ => ⟨y, hy, by
      have hl : x.val.length = 3 := by simpa using x.property
      match hx : x.val, hl with
      | [b0, b1, b2], _ => rw [hh b0 b1 b2 hx]; simp [U24.pval, hx]⟩

/-- `TlsByteVecU24::deserialize_bytes_bytes` never panics; on success the input is the 3-byte length prefix, the payload, then the remainder. -/
theorem tls_vec.TlsByteVecU24.deserialize_content (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU24.deserialize_bytes_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : tls_vec.TlsByteVecU24) (t : Slice Std.U8), r = .Ok (v, t) →
        ∃ b0 b1 b2 : Std.U8, b0.val * 65536 + b1.val * 256 + b2.val = v.vec.val.length ∧
          bytes.val = b0 :: b1 :: b2 :: (v.vec.val ++ t.val) ⌝ ⦄ := by
  rw [tls_vec.TlsByteVecU24.deserialize_bytes_bytes_eq]
  have hread := TlsByteVecGen.prefix_split (U := Aeneas.Std.Array Std.U8 3#usize) 3
    (fun a => a.val) (f := id) (fun _ => rfl) U24_deserialize_char
  refine total_of_pf_partial
    (TlsByteVecGen.pf _ _ _ (fun b => pf_of_total (hread b)) _ (fun p =>
      triple_post_mono (core.convert.TryFromTUInfallible.Blanket.try_from_Usize_U24_val p)
        fun _ ⟨y, hy, _⟩ => ⟨y, hy⟩) _ bytes) ?_
  refine partial_triple_of_ok fun r hr => ?_
  intro v t hv
  obtain ⟨p, hp, hb⟩ := ok_of_partial_triple
    (TlsByteVecGen.content tls_vec.TlsByteVecU24.vec _ (fun _ => rfl) (fun a => a.val) U24.pval 3#usize
      (fun a => a.property) _ hread _
      (fun p => partial_of_total (core.convert.TryFromTUInfallible.Blanket.try_from_Usize_U24_val p)) _ bytes) hr v t hv
  have hl : p.val.length = 3 := by simpa using p.property
  match hx : p.val, hl with
  | [b0, b1, b2], _ => exact ⟨b0, b1, b2, by simpa [U24.pval, hx] using hp, by simpa [hx] using hb⟩

/-- `TlsByteVecU24::deserialize_bytes_bytes` returns; on success the remainder plus the length prefix plus the payload is the input, and the payload is within the prefix bound. -/
theorem tls_vec.TlsByteVecU24.deserialize_char_le (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU24.deserialize_bytes_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : tls_vec.TlsByteVecU24) (t : Slice Std.U8), r = .Ok (v, t) →
        t.val.length + 3 + v.vec.val.length = bytes.val.length ∧
          v.vec.val.length ≤ 16777215 ⌝ ⦄ :=
  triple_post_mono (tls_vec.TlsByteVecU24.deserialize_content bytes) fun _ h v t hr => by
    obtain ⟨b0, b1, b2, hl, hb⟩ := h v t hr
    have := congrArg List.length hb
    simp only [List.length_cons, List.length_append] at this
    have := b0.hmax; have := b1.hmax; have := b2.hmax
    refine ⟨by omega, ?_⟩
    scalar_tac

theorem tls_vec.TlsByteVecU24.deserialize_char (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU24.deserialize_bytes_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : tls_vec.TlsByteVecU24) (t : Slice Std.U8), r = .Ok (v, t) →
        t.val.length + 3 + v.vec.val.length = bytes.val.length ⌝ ⦄ :=
  triple_post_mono (tls_vec.TlsByteVecU24.deserialize_char_le bytes) fun _ h v t hr => (h v t hr).1

/-- Partial form of `deserialize_char`. -/
theorem tls_vec.TlsByteVecU24.deserialize_char_partial (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsByteVecU24.deserialize_bytes_bytes bytes
    ⦃ ⇓? r => ⌜ ∀ (v : tls_vec.TlsByteVecU24) (t : Slice Std.U8), r = .Ok (v, t) →
        t.val.length + 3 + v.vec.val.length = bytes.val.length ⌝ ⦄ :=
  partial_of_total (tls_vec.TlsByteVecU24.deserialize_char bytes)

/-! #### `TlsVecU8` -/
@[spec] theorem tls_vec.TlsVecU8.push_spec {T : Type} (self : tls_vec.TlsVecU8 T) (x : T)
    (h : self.vec.val.length < Usize.max) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU8.push self x ⦃ ⇓ r => ⌜ r.vec.val = self.vec.val ++ [x] ⌝ ⦄ :=
  TlsVecGen.push_spec _ tls_vec.TlsVecU8.mk (fun _ => rfl) self x h

/-- The size of a `TlsVecU8` is the size fold of its elements, starting at the prefix width. -/
theorem tls_vec.TlsVecU8.size_rel {T : Type} (S : Size T) (hl : Size.Lawful T S)
    (self : tls_vec.TlsVecU8 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU8.tls_serialized_length S self
    ⦃ ⇓ r => ⌜ SizeFoldRel S 1#usize self.vec.val r ⌝ ⦄ :=
  TlsVecGen.serLen_rel S hl tls_vec.TlsVecU8.as_slice
    (fun x => alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref_spec x.vec) _ (fun _ _ _ => rfl) () 1#usize self

/-- `TlsVecU8::tls_serialized_length` does not fail when the element size does not. -/
theorem tls_vec.TlsVecU8.tls_serialized_length_pf {T : Type} (SizeInst : Size T)
    (SizeInstLawful : Size.Lawful T SizeInst) (self_ : tls_vec.TlsVecU8 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU8.tls_serialized_length SizeInst self_ ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  pf_of_total (tls_vec.TlsVecU8.size_rel SizeInst SizeInstLawful self_)

/-- `TlsVecU8::deserialize_bytes` is the generic one (rfl modulo the message literal). -/
theorem tls_vec.TlsVecU8.deserialize_bytes_eq {T : Type} :
    ∃ (M : Std.Usize) (pieces : Aeneas.Std.Array Std.U8 M), ∀ (inst : DeserializeBytes T),
      tls_vec.TlsVecU8.deserialize_bytes inst =
      TlsVecGen.deser tls_vec.TlsVecU8.mk U8.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes
        (core.convert.TryFromTUInfallible.Blanket.try_from
          (core.convert.Into.Blanket core.Usize.Insts.CoreConvertFromU8))
        core.convert.Infallible.Insts.CoreFmtDebug (tls_vec.TlsVecU8.deserialize_bytes_loop inst) pieces := by
  apply Exists.intro; apply Exists.intro; intro inst; funext bytes
  unfold tls_vec.TlsVecU8.deserialize_bytes TlsVecGen.deser
  congr 1; funext v; congr 1; funext r; congr 1; funext cf; cases cf <;> rfl

/-- `TlsVecU8::deserialize_bytes` from the trait contract of `T`: never fails to terminate, and an `Ok`
result accounts for the whole input (`rem.len + size v = bytes.len`). -/
theorem tls_vec.TlsVecU8.deserialize_bytes_char {T : Type} (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU8.deserialize_bytes inst bytes
    ⦃ ⇓ r => ⌜ ∀ v rem, r = .Ok (v, rem) → ∃ n,
        tls_vec.TlsVecU8.Insts.Tls_codecSize.tls_serialized_len inst.SizeInst v = ok n ∧
        rem.val.length + n.val = bytes.val.length ⌝ ⦄ := by
  obtain ⟨_, _, h⟩ := tls_vec.TlsVecU8.deserialize_bytes_eq (T := T)
  rw [h]
  exact TlsVecGen.deser_char inst.SizeInst _ _ (fun _ => rfl) _ 1#usize
    (tls_vec.TlsVecU8.size_rel inst.SizeInst hlaw.SizeInstLawful) _
    (TlsVecGen.prefix_len 1#usize 1 (by simp) U8_deserialize_char) _
    (TlsVecGen.conv_ok core.convert.TryFromTUInfallible.Blanket.try_from_Usize_U8_spec) _ _
    (fun N hN _ _ len _ hinv => TlsVecGen.loop_char _ _ tls_vec.TlsVecU8.push_spec inst len _ rfl
      hlaw 1#usize N hN _ _ _ hinv) _ bytes

/-- Functional correctness of `TlsVecU8::deserialize_bytes` (function-level post). -/
theorem tls_vec.TlsVecU8.deserialize_bytes_fc {T : Type} (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU8.deserialize_bytes inst bytes
    ⦃ ⇓? res => ⌜ (tls_vec.TlsVecU8.deserialize_bytes.post inst bytes res).holds ⌝ ⦄ :=
  TlsVecGen.fc_of_char _ bytes (tls_vec.TlsVecU8.deserialize_bytes_char inst hlaw bytes)

/-- `TlsVecU8::deserialize_bytes` does not fail. -/
theorem tls_vec.TlsVecU8.deserialize_bytes_pf {T : Type} (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU8.deserialize_bytes inst bytes ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  pf_of_total (tls_vec.TlsVecU8.deserialize_bytes_char inst hlaw bytes)


/-! #### `TlsVecU16` -/
@[spec] theorem tls_vec.TlsVecU16.push_spec {T : Type} (self : tls_vec.TlsVecU16 T) (x : T)
    (h : self.vec.val.length < Usize.max) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU16.push self x ⦃ ⇓ r => ⌜ r.vec.val = self.vec.val ++ [x] ⌝ ⦄ :=
  TlsVecGen.push_spec _ tls_vec.TlsVecU16.mk (fun _ => rfl) self x h

/-- The size of a `TlsVecU16` is the size fold of its elements, starting at the prefix width. -/
theorem tls_vec.TlsVecU16.size_rel {T : Type} (S : Size T) (hl : Size.Lawful T S)
    (self : tls_vec.TlsVecU16 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU16.tls_serialized_length S self
    ⦃ ⇓ r => ⌜ SizeFoldRel S 2#usize self.vec.val r ⌝ ⦄ :=
  TlsVecGen.serLen_rel S hl tls_vec.TlsVecU16.as_slice
    (fun x => alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref_spec x.vec) _ (fun _ _ _ => rfl) () 2#usize self

/-- `TlsVecU16::tls_serialized_length` does not fail when the element size does not. -/
theorem tls_vec.TlsVecU16.tls_serialized_length_pf {T : Type} (SizeInst : Size T)
    (SizeInstLawful : Size.Lawful T SizeInst) (self_ : tls_vec.TlsVecU16 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU16.tls_serialized_length SizeInst self_ ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  pf_of_total (tls_vec.TlsVecU16.size_rel SizeInst SizeInstLawful self_)

/-- `TlsVecU16::deserialize_bytes` is the generic one (rfl modulo the message literal). -/
theorem tls_vec.TlsVecU16.deserialize_bytes_eq {T : Type} :
    ∃ (M : Std.Usize) (pieces : Aeneas.Std.Array Std.U8 M), ∀ (inst : DeserializeBytes T),
      tls_vec.TlsVecU16.deserialize_bytes inst =
      TlsVecGen.deser tls_vec.TlsVecU16.mk U16.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes
        (core.convert.TryFromTUInfallible.Blanket.try_from
          (core.convert.Into.Blanket core.Usize.Insts.CoreConvertFromU16))
        core.convert.Infallible.Insts.CoreFmtDebug (tls_vec.TlsVecU16.deserialize_bytes_loop inst) pieces := by
  apply Exists.intro; apply Exists.intro; intro inst; funext bytes
  unfold tls_vec.TlsVecU16.deserialize_bytes TlsVecGen.deser
  congr 1; funext v; congr 1; funext r; congr 1; funext cf; cases cf <;> rfl

/-- `TlsVecU16::deserialize_bytes` from the trait contract of `T`: never fails to terminate, and an `Ok`
result accounts for the whole input (`rem.len + size v = bytes.len`). -/
theorem tls_vec.TlsVecU16.deserialize_bytes_char {T : Type} (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU16.deserialize_bytes inst bytes
    ⦃ ⇓ r => ⌜ ∀ v rem, r = .Ok (v, rem) → ∃ n,
        tls_vec.TlsVecU16.Insts.Tls_codecSize.tls_serialized_len inst.SizeInst v = ok n ∧
        rem.val.length + n.val = bytes.val.length ⌝ ⦄ := by
  obtain ⟨_, _, h⟩ := tls_vec.TlsVecU16.deserialize_bytes_eq (T := T)
  rw [h]
  exact TlsVecGen.deser_char inst.SizeInst _ _ (fun _ => rfl) _ 2#usize
    (tls_vec.TlsVecU16.size_rel inst.SizeInst hlaw.SizeInstLawful) _
    (TlsVecGen.prefix_len 2#usize 2 (by simp) U16_deserialize_char) _
    (TlsVecGen.conv_ok core.convert.TryFromTUInfallible.Blanket.try_from_Usize_U16_spec) _ _
    (fun N hN _ _ len _ hinv => TlsVecGen.loop_char _ _ tls_vec.TlsVecU16.push_spec inst len _ rfl
      hlaw 2#usize N hN _ _ _ hinv) _ bytes

/-- Functional correctness of `TlsVecU16::deserialize_bytes` (function-level post). -/
theorem tls_vec.TlsVecU16.deserialize_bytes_fc {T : Type} (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU16.deserialize_bytes inst bytes
    ⦃ ⇓? res => ⌜ (tls_vec.TlsVecU16.deserialize_bytes.post inst bytes res).holds ⌝ ⦄ :=
  TlsVecGen.fc_of_char _ bytes (tls_vec.TlsVecU16.deserialize_bytes_char inst hlaw bytes)

/-- `TlsVecU16::deserialize_bytes` does not fail. -/
theorem tls_vec.TlsVecU16.deserialize_bytes_pf {T : Type} (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU16.deserialize_bytes inst bytes ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  pf_of_total (tls_vec.TlsVecU16.deserialize_bytes_char inst hlaw bytes)


/-! #### `TlsVecU32` -/
@[spec] theorem tls_vec.TlsVecU32.push_spec {T : Type} (self : tls_vec.TlsVecU32 T) (x : T)
    (h : self.vec.val.length < Usize.max) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU32.push self x ⦃ ⇓ r => ⌜ r.vec.val = self.vec.val ++ [x] ⌝ ⦄ :=
  TlsVecGen.push_spec _ tls_vec.TlsVecU32.mk (fun _ => rfl) self x h

/-- The size of a `TlsVecU32` is the size fold of its elements, starting at the prefix width. -/
theorem tls_vec.TlsVecU32.size_rel {T : Type} (S : Size T) (hl : Size.Lawful T S)
    (self : tls_vec.TlsVecU32 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU32.tls_serialized_length S self
    ⦃ ⇓ r => ⌜ SizeFoldRel S 4#usize self.vec.val r ⌝ ⦄ :=
  TlsVecGen.serLen_rel S hl tls_vec.TlsVecU32.as_slice
    (fun x => alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref_spec x.vec) _ (fun _ _ _ => rfl) () 4#usize self

/-- `TlsVecU32::tls_serialized_length` does not fail when the element size does not. -/
theorem tls_vec.TlsVecU32.tls_serialized_length_pf {T : Type} (SizeInst : Size T)
    (SizeInstLawful : Size.Lawful T SizeInst) (self_ : tls_vec.TlsVecU32 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU32.tls_serialized_length SizeInst self_ ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  pf_of_total (tls_vec.TlsVecU32.size_rel SizeInst SizeInstLawful self_)

/-- `TlsVecU32::deserialize_bytes` is the generic one (rfl modulo the message literal). -/
theorem tls_vec.TlsVecU32.deserialize_bytes_eq {T : Type} :
    ∃ (M : Std.Usize) (pieces : Aeneas.Std.Array Std.U8 M), ∀ (inst : DeserializeBytes T),
      tls_vec.TlsVecU32.deserialize_bytes inst =
      TlsVecGen.deser tls_vec.TlsVecU32.mk U32.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes
        core.Usize.Insts.CoreConvertTryFromU32TryFromIntError.try_from
        core.num.error.TryFromIntError.Insts.CoreFmtDebug (tls_vec.TlsVecU32.deserialize_bytes_loop inst) pieces := by
  apply Exists.intro; apply Exists.intro; intro inst; funext bytes
  unfold tls_vec.TlsVecU32.deserialize_bytes TlsVecGen.deser
  congr 1; funext v; congr 1; funext r; congr 1; funext cf; cases cf <;> rfl

/-- `TlsVecU32::deserialize_bytes` from the trait contract of `T`: never fails to terminate, and an `Ok`
result accounts for the whole input (`rem.len + size v = bytes.len`). -/
theorem tls_vec.TlsVecU32.deserialize_bytes_char {T : Type} (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU32.deserialize_bytes inst bytes
    ⦃ ⇓ r => ⌜ ∀ v rem, r = .Ok (v, rem) → ∃ n,
        tls_vec.TlsVecU32.Insts.Tls_codecSize.tls_serialized_len inst.SizeInst v = ok n ∧
        rem.val.length + n.val = bytes.val.length ⌝ ⦄ := by
  obtain ⟨_, _, h⟩ := tls_vec.TlsVecU32.deserialize_bytes_eq (T := T)
  rw [h]
  exact TlsVecGen.deser_char inst.SizeInst _ _ (fun _ => rfl) _ 4#usize
    (tls_vec.TlsVecU32.size_rel inst.SizeInst hlaw.SizeInstLawful) _
    (TlsVecGen.prefix_len 4#usize 4 (by simp) U32_deserialize_char) _
    (TlsVecGen.conv_ok core.Usize.Insts.CoreConvertTryFromU32TryFromIntError.try_from_spec) _ _
    (fun N hN _ _ len _ hinv => TlsVecGen.loop_char _ _ tls_vec.TlsVecU32.push_spec inst len _ rfl
      hlaw 4#usize N hN _ _ _ hinv) _ bytes

/-- Functional correctness of `TlsVecU32::deserialize_bytes` (function-level post). -/
theorem tls_vec.TlsVecU32.deserialize_bytes_fc {T : Type} (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU32.deserialize_bytes inst bytes
    ⦃ ⇓? res => ⌜ (tls_vec.TlsVecU32.deserialize_bytes.post inst bytes res).holds ⌝ ⦄ :=
  TlsVecGen.fc_of_char _ bytes (tls_vec.TlsVecU32.deserialize_bytes_char inst hlaw bytes)

/-- `TlsVecU32::deserialize_bytes` does not fail. -/
theorem tls_vec.TlsVecU32.deserialize_bytes_pf {T : Type} (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU32.deserialize_bytes inst bytes ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  pf_of_total (tls_vec.TlsVecU32.deserialize_bytes_char inst hlaw bytes)


/-! #### `SecretTlsVecU8` -/

@[spec] theorem tls_vec.SecretTlsVecU8.push_spec {T : Type} (z : zeroize.Zeroize T) (self : tls_vec.SecretTlsVecU8 T) (x : T)
    (h : self.vec.val.length < Usize.max) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU8.push z self x ⦃ ⇓ r => ⌜ r.vec.val = self.vec.val ++ [x] ⌝ ⦄ :=
  TlsVecGen.push_spec _ tls_vec.SecretTlsVecU8.mk (fun _ => rfl) self x h

/-- The size of a `SecretTlsVecU8` is the size fold of its elements, starting at the prefix width. -/
theorem tls_vec.SecretTlsVecU8.size_rel {T : Type} (S : Size T) (z : zeroize.Zeroize T) (hl : Size.Lawful T S)
    (self : tls_vec.SecretTlsVecU8 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU8.tls_serialized_length S z self
    ⦃ ⇓ r => ⌜ SizeFoldRel S 1#usize self.vec.val r ⌝ ⦄ :=
  TlsVecGen.serLen_rel S hl (tls_vec.SecretTlsVecU8.as_slice z)
    (fun x => alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref_spec x.vec) _ (fun _ _ _ => rfl) () 1#usize self

/-- `SecretTlsVecU8::tls_serialized_length` does not fail when the element size does not. -/
theorem tls_vec.SecretTlsVecU8.tls_serialized_length_pf {T : Type} (SizeInst : Size T)
    (zeroizeZeroizeInst : zeroize.Zeroize T)
    (SizeInstLawful : Size.Lawful T SizeInst) (self_ : tls_vec.SecretTlsVecU8 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU8.tls_serialized_length SizeInst zeroizeZeroizeInst self_ ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  pf_of_total (tls_vec.SecretTlsVecU8.size_rel SizeInst zeroizeZeroizeInst SizeInstLawful self_)

/-- `SecretTlsVecU8::deserialize_bytes` is the generic one (rfl modulo the message literal). -/
theorem tls_vec.SecretTlsVecU8.deserialize_bytes_eq {T : Type} :
    ∃ (M : Std.Usize) (pieces : Aeneas.Std.Array Std.U8 M), ∀ (inst : DeserializeBytes T) (z : zeroize.Zeroize T),
      tls_vec.SecretTlsVecU8.deserialize_bytes inst z =
      TlsVecGen.deser tls_vec.SecretTlsVecU8.mk U8.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes
        (core.convert.TryFromTUInfallible.Blanket.try_from
          (core.convert.Into.Blanket core.Usize.Insts.CoreConvertFromU8))
        core.convert.Infallible.Insts.CoreFmtDebug (tls_vec.SecretTlsVecU8.deserialize_bytes_loop inst z) pieces := by
  apply Exists.intro; apply Exists.intro; intro inst z; funext bytes
  unfold tls_vec.SecretTlsVecU8.deserialize_bytes TlsVecGen.deser
  congr 1; funext v; congr 1; funext r; congr 1; funext cf; cases cf <;> rfl

/-- `SecretTlsVecU8::deserialize_bytes` from the trait contract of `T`: never fails to terminate, and an `Ok`
result accounts for the whole input (`rem.len + size v = bytes.len`). -/
theorem tls_vec.SecretTlsVecU8.deserialize_bytes_char {T : Type} (inst : DeserializeBytes T)
    (z : zeroize.Zeroize T) (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU8.deserialize_bytes inst z bytes
    ⦃ ⇓ r => ⌜ ∀ v rem, r = .Ok (v, rem) → ∃ n,
        tls_vec.SecretTlsVecU8.Insts.Tls_codecSize.tls_serialized_len z inst.SizeInst v = ok n ∧
        rem.val.length + n.val = bytes.val.length ⌝ ⦄ := by
  obtain ⟨_, _, h⟩ := tls_vec.SecretTlsVecU8.deserialize_bytes_eq (T := T)
  rw [h]
  exact TlsVecGen.deser_char inst.SizeInst _ _ (fun _ => rfl) _ 1#usize
    (tls_vec.SecretTlsVecU8.size_rel inst.SizeInst z hlaw.SizeInstLawful) _
    (TlsVecGen.prefix_len 1#usize 1 (by simp) U8_deserialize_char) _
    (TlsVecGen.conv_ok core.convert.TryFromTUInfallible.Blanket.try_from_Usize_U8_spec) _ _
    (fun N hN _ _ len _ hinv => TlsVecGen.loop_char _ _ (tls_vec.SecretTlsVecU8.push_spec z) inst len _ rfl
      hlaw 1#usize N hN _ _ _ hinv) _ bytes

/-- Functional correctness of `SecretTlsVecU8::deserialize_bytes` (function-level post). -/
theorem tls_vec.SecretTlsVecU8.deserialize_bytes_fc {T : Type} (inst : DeserializeBytes T)
    (z : zeroize.Zeroize T) (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU8.deserialize_bytes inst z bytes
    ⦃ ⇓? res => ⌜ (tls_vec.SecretTlsVecU8.deserialize_bytes.post inst z bytes res).holds ⌝ ⦄ :=
  TlsVecGen.fc_of_char _ bytes (tls_vec.SecretTlsVecU8.deserialize_bytes_char inst z hlaw bytes)

/-- `SecretTlsVecU8::deserialize_bytes` does not fail. -/
theorem tls_vec.SecretTlsVecU8.deserialize_bytes_pf {T : Type} (inst : DeserializeBytes T)
    (z : zeroize.Zeroize T) (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU8.deserialize_bytes inst z bytes ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  pf_of_total (tls_vec.SecretTlsVecU8.deserialize_bytes_char inst z hlaw bytes)

/-! #### `SecretTlsVecU16` -/

@[spec] theorem tls_vec.SecretTlsVecU16.push_spec {T : Type} (z : zeroize.Zeroize T) (self : tls_vec.SecretTlsVecU16 T) (x : T)
    (h : self.vec.val.length < Usize.max) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU16.push z self x ⦃ ⇓ r => ⌜ r.vec.val = self.vec.val ++ [x] ⌝ ⦄ :=
  TlsVecGen.push_spec _ tls_vec.SecretTlsVecU16.mk (fun _ => rfl) self x h

/-- The size of a `SecretTlsVecU16` is the size fold of its elements, starting at the prefix width. -/
theorem tls_vec.SecretTlsVecU16.size_rel {T : Type} (S : Size T) (z : zeroize.Zeroize T) (hl : Size.Lawful T S)
    (self : tls_vec.SecretTlsVecU16 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU16.tls_serialized_length S z self
    ⦃ ⇓ r => ⌜ SizeFoldRel S 2#usize self.vec.val r ⌝ ⦄ :=
  TlsVecGen.serLen_rel S hl (tls_vec.SecretTlsVecU16.as_slice z)
    (fun x => alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref_spec x.vec) _ (fun _ _ _ => rfl) () 2#usize self

/-- `SecretTlsVecU16::tls_serialized_length` does not fail when the element size does not. -/
theorem tls_vec.SecretTlsVecU16.tls_serialized_length_pf {T : Type} (SizeInst : Size T)
    (zeroizeZeroizeInst : zeroize.Zeroize T)
    (SizeInstLawful : Size.Lawful T SizeInst) (self_ : tls_vec.SecretTlsVecU16 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU16.tls_serialized_length SizeInst zeroizeZeroizeInst self_ ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  pf_of_total (tls_vec.SecretTlsVecU16.size_rel SizeInst zeroizeZeroizeInst SizeInstLawful self_)

/-- `SecretTlsVecU16::deserialize_bytes` is the generic one (rfl modulo the message literal). -/
theorem tls_vec.SecretTlsVecU16.deserialize_bytes_eq {T : Type} :
    ∃ (M : Std.Usize) (pieces : Aeneas.Std.Array Std.U8 M), ∀ (inst : DeserializeBytes T) (z : zeroize.Zeroize T),
      tls_vec.SecretTlsVecU16.deserialize_bytes inst z =
      TlsVecGen.deser tls_vec.SecretTlsVecU16.mk U16.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes
        (core.convert.TryFromTUInfallible.Blanket.try_from
          (core.convert.Into.Blanket core.Usize.Insts.CoreConvertFromU16))
        core.convert.Infallible.Insts.CoreFmtDebug (tls_vec.SecretTlsVecU16.deserialize_bytes_loop inst z) pieces := by
  apply Exists.intro; apply Exists.intro; intro inst z; funext bytes
  unfold tls_vec.SecretTlsVecU16.deserialize_bytes TlsVecGen.deser
  congr 1; funext v; congr 1; funext r; congr 1; funext cf; cases cf <;> rfl

/-- `SecretTlsVecU16::deserialize_bytes` from the trait contract of `T`: never fails to terminate, and an `Ok`
result accounts for the whole input (`rem.len + size v = bytes.len`). -/
theorem tls_vec.SecretTlsVecU16.deserialize_bytes_char {T : Type} (inst : DeserializeBytes T)
    (z : zeroize.Zeroize T) (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU16.deserialize_bytes inst z bytes
    ⦃ ⇓ r => ⌜ ∀ v rem, r = .Ok (v, rem) → ∃ n,
        tls_vec.SecretTlsVecU16.Insts.Tls_codecSize.tls_serialized_len z inst.SizeInst v = ok n ∧
        rem.val.length + n.val = bytes.val.length ⌝ ⦄ := by
  obtain ⟨_, _, h⟩ := tls_vec.SecretTlsVecU16.deserialize_bytes_eq (T := T)
  rw [h]
  exact TlsVecGen.deser_char inst.SizeInst _ _ (fun _ => rfl) _ 2#usize
    (tls_vec.SecretTlsVecU16.size_rel inst.SizeInst z hlaw.SizeInstLawful) _
    (TlsVecGen.prefix_len 2#usize 2 (by simp) U16_deserialize_char) _
    (TlsVecGen.conv_ok core.convert.TryFromTUInfallible.Blanket.try_from_Usize_U16_spec) _ _
    (fun N hN _ _ len _ hinv => TlsVecGen.loop_char _ _ (tls_vec.SecretTlsVecU16.push_spec z) inst len _ rfl
      hlaw 2#usize N hN _ _ _ hinv) _ bytes

/-- Functional correctness of `SecretTlsVecU16::deserialize_bytes` (function-level post). -/
theorem tls_vec.SecretTlsVecU16.deserialize_bytes_fc {T : Type} (inst : DeserializeBytes T)
    (z : zeroize.Zeroize T) (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU16.deserialize_bytes inst z bytes
    ⦃ ⇓? res => ⌜ (tls_vec.SecretTlsVecU16.deserialize_bytes.post inst z bytes res).holds ⌝ ⦄ :=
  TlsVecGen.fc_of_char _ bytes (tls_vec.SecretTlsVecU16.deserialize_bytes_char inst z hlaw bytes)

/-- `SecretTlsVecU16::deserialize_bytes` does not fail. -/
theorem tls_vec.SecretTlsVecU16.deserialize_bytes_pf {T : Type} (inst : DeserializeBytes T)
    (z : zeroize.Zeroize T) (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU16.deserialize_bytes inst z bytes ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  pf_of_total (tls_vec.SecretTlsVecU16.deserialize_bytes_char inst z hlaw bytes)

/-! #### `SecretTlsVecU32` -/

@[spec] theorem tls_vec.SecretTlsVecU32.push_spec {T : Type} (z : zeroize.Zeroize T) (self : tls_vec.SecretTlsVecU32 T) (x : T)
    (h : self.vec.val.length < Usize.max) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU32.push z self x ⦃ ⇓ r => ⌜ r.vec.val = self.vec.val ++ [x] ⌝ ⦄ :=
  TlsVecGen.push_spec _ tls_vec.SecretTlsVecU32.mk (fun _ => rfl) self x h

/-- The size of a `SecretTlsVecU32` is the size fold of its elements, starting at the prefix width. -/
theorem tls_vec.SecretTlsVecU32.size_rel {T : Type} (S : Size T) (z : zeroize.Zeroize T) (hl : Size.Lawful T S)
    (self : tls_vec.SecretTlsVecU32 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU32.tls_serialized_length S z self
    ⦃ ⇓ r => ⌜ SizeFoldRel S 4#usize self.vec.val r ⌝ ⦄ :=
  TlsVecGen.serLen_rel S hl (tls_vec.SecretTlsVecU32.as_slice z)
    (fun x => alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref_spec x.vec) _ (fun _ _ _ => rfl) () 4#usize self

/-- `SecretTlsVecU32::tls_serialized_length` does not fail when the element size does not. -/
theorem tls_vec.SecretTlsVecU32.tls_serialized_length_pf {T : Type} (SizeInst : Size T)
    (zeroizeZeroizeInst : zeroize.Zeroize T)
    (SizeInstLawful : Size.Lawful T SizeInst) (self_ : tls_vec.SecretTlsVecU32 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU32.tls_serialized_length SizeInst zeroizeZeroizeInst self_ ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  pf_of_total (tls_vec.SecretTlsVecU32.size_rel SizeInst zeroizeZeroizeInst SizeInstLawful self_)

/-- `SecretTlsVecU32::deserialize_bytes` is the generic one (rfl modulo the message literal). -/
theorem tls_vec.SecretTlsVecU32.deserialize_bytes_eq {T : Type} :
    ∃ (M : Std.Usize) (pieces : Aeneas.Std.Array Std.U8 M), ∀ (inst : DeserializeBytes T) (z : zeroize.Zeroize T),
      tls_vec.SecretTlsVecU32.deserialize_bytes inst z =
      TlsVecGen.deser tls_vec.SecretTlsVecU32.mk U32.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes
        core.Usize.Insts.CoreConvertTryFromU32TryFromIntError.try_from
        core.num.error.TryFromIntError.Insts.CoreFmtDebug (tls_vec.SecretTlsVecU32.deserialize_bytes_loop inst z) pieces := by
  apply Exists.intro; apply Exists.intro; intro inst z; funext bytes
  unfold tls_vec.SecretTlsVecU32.deserialize_bytes TlsVecGen.deser
  congr 1; funext v; congr 1; funext r; congr 1; funext cf; cases cf <;> rfl

/-- `SecretTlsVecU32::deserialize_bytes` from the trait contract of `T`: never fails to terminate, and an `Ok`
result accounts for the whole input (`rem.len + size v = bytes.len`). -/
theorem tls_vec.SecretTlsVecU32.deserialize_bytes_char {T : Type} (inst : DeserializeBytes T)
    (z : zeroize.Zeroize T) (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU32.deserialize_bytes inst z bytes
    ⦃ ⇓ r => ⌜ ∀ v rem, r = .Ok (v, rem) → ∃ n,
        tls_vec.SecretTlsVecU32.Insts.Tls_codecSize.tls_serialized_len z inst.SizeInst v = ok n ∧
        rem.val.length + n.val = bytes.val.length ⌝ ⦄ := by
  obtain ⟨_, _, h⟩ := tls_vec.SecretTlsVecU32.deserialize_bytes_eq (T := T)
  rw [h]
  exact TlsVecGen.deser_char inst.SizeInst _ _ (fun _ => rfl) _ 4#usize
    (tls_vec.SecretTlsVecU32.size_rel inst.SizeInst z hlaw.SizeInstLawful) _
    (TlsVecGen.prefix_len 4#usize 4 (by simp) U32_deserialize_char) _
    (TlsVecGen.conv_ok core.Usize.Insts.CoreConvertTryFromU32TryFromIntError.try_from_spec) _ _
    (fun N hN _ _ len _ hinv => TlsVecGen.loop_char _ _ (tls_vec.SecretTlsVecU32.push_spec z) inst len _ rfl
      hlaw 4#usize N hN _ _ _ hinv) _ bytes

/-- Functional correctness of `SecretTlsVecU32::deserialize_bytes` (function-level post). -/
theorem tls_vec.SecretTlsVecU32.deserialize_bytes_fc {T : Type} (inst : DeserializeBytes T)
    (z : zeroize.Zeroize T) (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU32.deserialize_bytes inst z bytes
    ⦃ ⇓? res => ⌜ (tls_vec.SecretTlsVecU32.deserialize_bytes.post inst z bytes res).holds ⌝ ⦄ :=
  TlsVecGen.fc_of_char _ bytes (tls_vec.SecretTlsVecU32.deserialize_bytes_char inst z hlaw bytes)

/-- `SecretTlsVecU32::deserialize_bytes` does not fail. -/
theorem tls_vec.SecretTlsVecU32.deserialize_bytes_pf {T : Type} (inst : DeserializeBytes T)
    (z : zeroize.Zeroize T) (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU32.deserialize_bytes inst z bytes ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  pf_of_total (tls_vec.SecretTlsVecU32.deserialize_bytes_char inst z hlaw bytes)

/-! #### `TlsVecU24` -/

@[spec] theorem tls_vec.TlsVecU24.push_spec {T : Type} (self : tls_vec.TlsVecU24 T) (x : T)
    (h : self.vec.val.length < Usize.max) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU24.push self x ⦃ ⇓ r => ⌜ r.vec.val = self.vec.val ++ [x] ⌝ ⦄ :=
  TlsVecGen.push_spec _ tls_vec.TlsVecU24.mk (fun _ => rfl) self x h

/-- The size of a `TlsVecU24` is the size fold of its elements, starting at the prefix width. -/
theorem tls_vec.TlsVecU24.size_rel {T : Type} (S : Size T) (hl : Size.Lawful T S)
    (self : tls_vec.TlsVecU24 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU24.tls_serialized_length S self
    ⦃ ⇓ r => ⌜ SizeFoldRel S 3#usize self.vec.val r ⌝ ⦄ :=
  TlsVecGen.serLen_rel S hl tls_vec.TlsVecU24.as_slice
    (fun x => alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref_spec x.vec) _ (fun _ _ _ => rfl) () 3#usize self

/-- `TlsVecU24::tls_serialized_length` does not fail when the element size does not. -/
theorem tls_vec.TlsVecU24.tls_serialized_length_pf {T : Type} (SizeInst : Size T)
    (SizeInstLawful : Size.Lawful T SizeInst) (self_ : tls_vec.TlsVecU24 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU24.tls_serialized_length SizeInst self_ ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  pf_of_total (tls_vec.TlsVecU24.size_rel SizeInst SizeInstLawful self_)

/-- `TlsVecU24::deserialize_bytes` is the generic one (rfl modulo the message literal). -/
theorem tls_vec.TlsVecU24.deserialize_bytes_eq {T : Type} :
    ∃ (M : Std.Usize) (pieces : Aeneas.Std.Array Std.U8 M), ∀ (inst : DeserializeBytes T),
      tls_vec.TlsVecU24.deserialize_bytes inst =
      TlsVecGen.deser tls_vec.TlsVecU24.mk U24.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes
        (core.convert.TryFromTUInfallible.Blanket.try_from
          (core.convert.Into.Blanket Usize.Insts.CoreConvertFromU24))
        core.convert.Infallible.Insts.CoreFmtDebug (tls_vec.TlsVecU24.deserialize_bytes_loop inst) pieces := by
  apply Exists.intro; apply Exists.intro; intro inst; funext bytes
  unfold tls_vec.TlsVecU24.deserialize_bytes TlsVecGen.deser
  congr 1; funext v; congr 1; funext r; congr 1; funext cf; cases cf <;> rfl

/-- `TlsVecU24::deserialize_bytes` from the trait contract of `T`: never fails to terminate, and an `Ok`
result accounts for the whole input (`rem.len + size v = bytes.len`). -/
theorem tls_vec.TlsVecU24.deserialize_bytes_char {T : Type} (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU24.deserialize_bytes inst bytes
    ⦃ ⇓ r => ⌜ ∀ v rem, r = .Ok (v, rem) → ∃ n,
        tls_vec.TlsVecU24.Insts.Tls_codecSize.tls_serialized_len inst.SizeInst v = ok n ∧
        rem.val.length + n.val = bytes.val.length ⌝ ⦄ := by
  obtain ⟨_, _, h⟩ := tls_vec.TlsVecU24.deserialize_bytes_eq (T := T)
  rw [h]
  exact TlsVecGen.deser_char inst.SizeInst _ _ (fun _ => rfl) _ 3#usize
    (tls_vec.TlsVecU24.size_rel inst.SizeInst hlaw.SizeInstLawful) _
    (TlsVecGen.prefix_len 3#usize 3 (by simp) U24_deserialize_char) _
    (core.convert.TryFromTUInfallible.Blanket.try_from_Usize_U24_ok) _ _
    (fun N hN _ _ len _ hinv => TlsVecGen.loop_char _ _ tls_vec.TlsVecU24.push_spec inst len _ rfl
      hlaw 3#usize N hN _ _ _ hinv) _ bytes

/-- Functional correctness of `TlsVecU24::deserialize_bytes` (function-level post). -/
theorem tls_vec.TlsVecU24.deserialize_bytes_fc {T : Type} (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU24.deserialize_bytes inst bytes
    ⦃ ⇓? res => ⌜ (tls_vec.TlsVecU24.deserialize_bytes.post inst bytes res).holds ⌝ ⦄ :=
  TlsVecGen.fc_of_char _ bytes (tls_vec.TlsVecU24.deserialize_bytes_char inst hlaw bytes)

/-- `TlsVecU24::deserialize_bytes` does not fail. -/
theorem tls_vec.TlsVecU24.deserialize_bytes_pf {T : Type} (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.TlsVecU24.deserialize_bytes inst bytes ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  pf_of_total (tls_vec.TlsVecU24.deserialize_bytes_char inst hlaw bytes)

/-! #### `SecretTlsVecU24` -/

@[spec] theorem tls_vec.SecretTlsVecU24.push_spec {T : Type} (z : zeroize.Zeroize T) (self : tls_vec.SecretTlsVecU24 T) (x : T)
    (h : self.vec.val.length < Usize.max) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU24.push z self x ⦃ ⇓ r => ⌜ r.vec.val = self.vec.val ++ [x] ⌝ ⦄ :=
  TlsVecGen.push_spec _ tls_vec.SecretTlsVecU24.mk (fun _ => rfl) self x h

/-- The size of a `SecretTlsVecU24` is the size fold of its elements, starting at the prefix width. -/
theorem tls_vec.SecretTlsVecU24.size_rel {T : Type} (S : Size T) (z : zeroize.Zeroize T) (hl : Size.Lawful T S)
    (self : tls_vec.SecretTlsVecU24 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU24.tls_serialized_length S z self
    ⦃ ⇓ r => ⌜ SizeFoldRel S 3#usize self.vec.val r ⌝ ⦄ :=
  TlsVecGen.serLen_rel S hl (tls_vec.SecretTlsVecU24.as_slice z)
    (fun x => alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref_spec x.vec) _ (fun _ _ _ => rfl) () 3#usize self

/-- `SecretTlsVecU24::tls_serialized_length` does not fail when the element size does not. -/
theorem tls_vec.SecretTlsVecU24.tls_serialized_length_pf {T : Type} (SizeInst : Size T)
    (zeroizeZeroizeInst : zeroize.Zeroize T)
    (SizeInstLawful : Size.Lawful T SizeInst) (self_ : tls_vec.SecretTlsVecU24 T) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU24.tls_serialized_length SizeInst zeroizeZeroizeInst self_ ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  pf_of_total (tls_vec.SecretTlsVecU24.size_rel SizeInst zeroizeZeroizeInst SizeInstLawful self_)

/-- `SecretTlsVecU24::deserialize_bytes` is the generic one (rfl modulo the message literal). -/
theorem tls_vec.SecretTlsVecU24.deserialize_bytes_eq {T : Type} :
    ∃ (M : Std.Usize) (pieces : Aeneas.Std.Array Std.U8 M), ∀ (inst : DeserializeBytes T) (z : zeroize.Zeroize T),
      tls_vec.SecretTlsVecU24.deserialize_bytes inst z =
      TlsVecGen.deser tls_vec.SecretTlsVecU24.mk U24.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes
        (core.convert.TryFromTUInfallible.Blanket.try_from
          (core.convert.Into.Blanket Usize.Insts.CoreConvertFromU24))
        core.convert.Infallible.Insts.CoreFmtDebug (tls_vec.SecretTlsVecU24.deserialize_bytes_loop inst z) pieces := by
  apply Exists.intro; apply Exists.intro; intro inst z; funext bytes
  unfold tls_vec.SecretTlsVecU24.deserialize_bytes TlsVecGen.deser
  congr 1; funext v; congr 1; funext r; congr 1; funext cf; cases cf <;> rfl

/-- `SecretTlsVecU24::deserialize_bytes` from the trait contract of `T`: never fails to terminate, and an `Ok`
result accounts for the whole input (`rem.len + size v = bytes.len`). -/
theorem tls_vec.SecretTlsVecU24.deserialize_bytes_char {T : Type} (inst : DeserializeBytes T)
    (z : zeroize.Zeroize T) (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU24.deserialize_bytes inst z bytes
    ⦃ ⇓ r => ⌜ ∀ v rem, r = .Ok (v, rem) → ∃ n,
        tls_vec.SecretTlsVecU24.Insts.Tls_codecSize.tls_serialized_len z inst.SizeInst v = ok n ∧
        rem.val.length + n.val = bytes.val.length ⌝ ⦄ := by
  obtain ⟨_, _, h⟩ := tls_vec.SecretTlsVecU24.deserialize_bytes_eq (T := T)
  rw [h]
  exact TlsVecGen.deser_char inst.SizeInst _ _ (fun _ => rfl) _ 3#usize
    (tls_vec.SecretTlsVecU24.size_rel inst.SizeInst z hlaw.SizeInstLawful) _
    (TlsVecGen.prefix_len 3#usize 3 (by simp) U24_deserialize_char) _
    (core.convert.TryFromTUInfallible.Blanket.try_from_Usize_U24_ok) _ _
    (fun N hN _ _ len _ hinv => TlsVecGen.loop_char _ _ (tls_vec.SecretTlsVecU24.push_spec z) inst len _ rfl
      hlaw 3#usize N hN _ _ _ hinv) _ bytes

/-- Functional correctness of `SecretTlsVecU24::deserialize_bytes` (function-level post). -/
theorem tls_vec.SecretTlsVecU24.deserialize_bytes_fc {T : Type} (inst : DeserializeBytes T)
    (z : zeroize.Zeroize T) (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU24.deserialize_bytes inst z bytes
    ⦃ ⇓? res => ⌜ (tls_vec.SecretTlsVecU24.deserialize_bytes.post inst z bytes res).holds ⌝ ⦄ :=
  TlsVecGen.fc_of_char _ bytes (tls_vec.SecretTlsVecU24.deserialize_bytes_char inst z hlaw bytes)

/-- `SecretTlsVecU24::deserialize_bytes` does not fail. -/
theorem tls_vec.SecretTlsVecU24.deserialize_bytes_pf {T : Type} (inst : DeserializeBytes T)
    (z : zeroize.Zeroize T) (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ tls_vec.SecretTlsVecU24.deserialize_bytes inst z bytes ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  pf_of_total (tls_vec.SecretTlsVecU24.deserialize_bytes_char inst z hlaw bytes)

/-! #### From a characterization of the result to the trait-level post -/

/-- A result `r` meeting `∀ v rem, r = Ok (v, rem) → ∃ n, size v = n ∧ rem.len + n = bytes.len` meets the
trait-level post of `tls_deserialize_bytes`. -/
theorem DeserializeBytes.post_of_char {Self : Type} (S : Size Self) (inst : DeserializeBytes Self)
    (bytes : Slice Std.U8) (r : core.result.Result (Self × Slice Std.U8) Error)
    (h : ∀ v rem, r = .Ok (v, rem) → ∃ n, S.tls_serialized_len v = ok n ∧
      rem.val.length + n.val = bytes.val.length) :
    (DeserializeBytes.tls_deserialize_bytes.post S inst bytes r).holds := by
  cases r with
  | Err e => exact DeserializeBytes.post_err S inst bytes e
  | Ok p =>
    obtain ⟨v, rem⟩ := p
    obtain ⟨n, hn, hr⟩ := h v rem rfl
    exact DeserializeBytes.post_ok S inst bytes v rem n hn hr

/-- Total characterization of a `tls_deserialize_bytes`-shaped program gives the trait-level post
(as a partial triple). -/
theorem DeserializeBytes.fc_of_char {Self : Type} (S : Size Self) (inst : DeserializeBytes Self)
    (bytes : Slice Std.U8) (m : RustM (core.result.Result (Self × Slice Std.U8) Error))
    (h : ⦃ ⌜ True ⌝ ⦄ m ⦃ ⇓ r => ⌜ ∀ v rem, r = .Ok (v, rem) → ∃ n, S.tls_serialized_len v = ok n ∧
      rem.val.length + n.val = bytes.val.length ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄ m ⦃ ⇓? res => ⌜ (DeserializeBytes.tls_deserialize_bytes.post S inst bytes res).holds ⌝ ⦄ := by
  obtain ⟨v, hv, hP⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp h
  rw [hv]
  apply RustM.ok_spec
  exact DeserializeBytes.post_of_char S inst bytes v hP

/-- As `DeserializeBytes.fc_of_char`, from a partial characterization. -/
theorem DeserializeBytes.fc_of_char_partial {Self : Type} (S : Size Self) (inst : DeserializeBytes Self)
    (bytes : Slice Std.U8) (m : RustM (core.result.Result (Self × Slice Std.U8) Error))
    (h : ⦃ ⌜ True ⌝ ⦄ m ⦃ ⇓? r => ⌜ ∀ v rem, r = .Ok (v, rem) → ∃ n, S.tls_serialized_len v = ok n ∧
      rem.val.length + n.val = bytes.val.length ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄ m ⦃ ⇓? res => ⌜ (DeserializeBytes.tls_deserialize_bytes.post S inst bytes res).holds ⌝ ⦄ := by
  apply partial_triple_of_ok
  intro r hr
  exact DeserializeBytes.post_of_char S inst bytes r (ok_of_partial_triple h hr)

/-! #### `TlsVecU8`: function and trait-level specs -/

/-- Functional correctness of the trait method of `TlsVecU8` (trait-level post). -/
theorem tls_vec.TlsVecU8.trait_fc {T : Type} (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
      (tls_vec.TlsVecU8.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes inst) bytes
    ⦃ ⇓? res => ⌜ (DeserializeBytes.tls_deserialize_bytes.post
        (tls_vec.TlsVecU8.Insts.Tls_codecDeserializeBytes inst).SizeInst
        (tls_vec.TlsVecU8.Insts.Tls_codecDeserializeBytes inst) bytes res).holds ⌝ ⦄ :=
  DeserializeBytes.fc_of_char (tls_vec.TlsVecU8.Insts.Tls_codecSize inst.SizeInst)
    (tls_vec.TlsVecU8.Insts.Tls_codecDeserializeBytes inst) bytes _
    (tls_vec.TlsVecU8.deserialize_bytes_char inst hlaw bytes)

/-- The trait method of `TlsVecU8` does not fail. -/
theorem tls_vec.TlsVecU8.trait_pf {T : Type} (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
      (tls_vec.TlsVecU8.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes inst) bytes
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  tls_vec.TlsVecU8.deserialize_bytes_pf inst hlaw bytes

/-! #### `TlsVecU16`: function and trait-level specs -/

/-- Functional correctness of the trait method of `TlsVecU16` (trait-level post). -/
theorem tls_vec.TlsVecU16.trait_fc {T : Type} (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
      (tls_vec.TlsVecU16.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes inst) bytes
    ⦃ ⇓? res => ⌜ (DeserializeBytes.tls_deserialize_bytes.post
        (tls_vec.TlsVecU16.Insts.Tls_codecDeserializeBytes inst).SizeInst
        (tls_vec.TlsVecU16.Insts.Tls_codecDeserializeBytes inst) bytes res).holds ⌝ ⦄ :=
  DeserializeBytes.fc_of_char (tls_vec.TlsVecU16.Insts.Tls_codecSize inst.SizeInst)
    (tls_vec.TlsVecU16.Insts.Tls_codecDeserializeBytes inst) bytes _
    (tls_vec.TlsVecU16.deserialize_bytes_char inst hlaw bytes)

/-- The trait method of `TlsVecU16` does not fail. -/
theorem tls_vec.TlsVecU16.trait_pf {T : Type} (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
      (tls_vec.TlsVecU16.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes inst) bytes
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  tls_vec.TlsVecU16.deserialize_bytes_pf inst hlaw bytes

/-! #### `TlsVecU24`: function and trait-level specs -/

/-- Functional correctness of the trait method of `TlsVecU24` (trait-level post). -/
theorem tls_vec.TlsVecU24.trait_fc {T : Type} (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
      (tls_vec.TlsVecU24.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes inst) bytes
    ⦃ ⇓? res => ⌜ (DeserializeBytes.tls_deserialize_bytes.post
        (tls_vec.TlsVecU24.Insts.Tls_codecDeserializeBytes inst).SizeInst
        (tls_vec.TlsVecU24.Insts.Tls_codecDeserializeBytes inst) bytes res).holds ⌝ ⦄ :=
  DeserializeBytes.fc_of_char (tls_vec.TlsVecU24.Insts.Tls_codecSize inst.SizeInst)
    (tls_vec.TlsVecU24.Insts.Tls_codecDeserializeBytes inst) bytes _
    (tls_vec.TlsVecU24.deserialize_bytes_char inst hlaw bytes)

/-- The trait method of `TlsVecU24` does not fail. -/
theorem tls_vec.TlsVecU24.trait_pf {T : Type} (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
      (tls_vec.TlsVecU24.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes inst) bytes
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  tls_vec.TlsVecU24.deserialize_bytes_pf inst hlaw bytes

/-! #### `TlsVecU32`: function and trait-level specs -/

/-- Functional correctness of the trait method of `TlsVecU32` (trait-level post). -/
theorem tls_vec.TlsVecU32.trait_fc {T : Type} (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
      (tls_vec.TlsVecU32.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes inst) bytes
    ⦃ ⇓? res => ⌜ (DeserializeBytes.tls_deserialize_bytes.post
        (tls_vec.TlsVecU32.Insts.Tls_codecDeserializeBytes inst).SizeInst
        (tls_vec.TlsVecU32.Insts.Tls_codecDeserializeBytes inst) bytes res).holds ⌝ ⦄ :=
  DeserializeBytes.fc_of_char (tls_vec.TlsVecU32.Insts.Tls_codecSize inst.SizeInst)
    (tls_vec.TlsVecU32.Insts.Tls_codecDeserializeBytes inst) bytes _
    (tls_vec.TlsVecU32.deserialize_bytes_char inst hlaw bytes)

/-- The trait method of `TlsVecU32` does not fail. -/
theorem tls_vec.TlsVecU32.trait_pf {T : Type} (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
      (tls_vec.TlsVecU32.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes inst) bytes
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  tls_vec.TlsVecU32.deserialize_bytes_pf inst hlaw bytes

/-! #### `SecretTlsVecU8`: function and trait-level specs -/

/-- Functional correctness of the trait method of `SecretTlsVecU8` (trait-level post). -/
theorem tls_vec.SecretTlsVecU8.trait_fc {T : Type} (inst : DeserializeBytes T)
    (z : zeroize.Zeroize T) (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
      (tls_vec.SecretTlsVecU8.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes z inst) bytes
    ⦃ ⇓? res => ⌜ (DeserializeBytes.tls_deserialize_bytes.post
        (tls_vec.SecretTlsVecU8.Insts.Tls_codecDeserializeBytes z inst).SizeInst
        (tls_vec.SecretTlsVecU8.Insts.Tls_codecDeserializeBytes z inst) bytes res).holds ⌝ ⦄ :=
  DeserializeBytes.fc_of_char (tls_vec.SecretTlsVecU8.Insts.Tls_codecSize z inst.SizeInst)
    (tls_vec.SecretTlsVecU8.Insts.Tls_codecDeserializeBytes z inst) bytes _
    (tls_vec.SecretTlsVecU8.deserialize_bytes_char inst z hlaw bytes)

/-- The trait method of `SecretTlsVecU8` does not fail. -/
theorem tls_vec.SecretTlsVecU8.trait_pf {T : Type} (inst : DeserializeBytes T)
    (z : zeroize.Zeroize T) (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
      (tls_vec.SecretTlsVecU8.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes z inst) bytes
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  tls_vec.SecretTlsVecU8.deserialize_bytes_pf inst z hlaw bytes

/-! #### `SecretTlsVecU16`: function and trait-level specs -/

/-- Functional correctness of the trait method of `SecretTlsVecU16` (trait-level post). -/
theorem tls_vec.SecretTlsVecU16.trait_fc {T : Type} (inst : DeserializeBytes T)
    (z : zeroize.Zeroize T) (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
      (tls_vec.SecretTlsVecU16.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes z inst) bytes
    ⦃ ⇓? res => ⌜ (DeserializeBytes.tls_deserialize_bytes.post
        (tls_vec.SecretTlsVecU16.Insts.Tls_codecDeserializeBytes z inst).SizeInst
        (tls_vec.SecretTlsVecU16.Insts.Tls_codecDeserializeBytes z inst) bytes res).holds ⌝ ⦄ :=
  DeserializeBytes.fc_of_char (tls_vec.SecretTlsVecU16.Insts.Tls_codecSize z inst.SizeInst)
    (tls_vec.SecretTlsVecU16.Insts.Tls_codecDeserializeBytes z inst) bytes _
    (tls_vec.SecretTlsVecU16.deserialize_bytes_char inst z hlaw bytes)

/-- The trait method of `SecretTlsVecU16` does not fail. -/
theorem tls_vec.SecretTlsVecU16.trait_pf {T : Type} (inst : DeserializeBytes T)
    (z : zeroize.Zeroize T) (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
      (tls_vec.SecretTlsVecU16.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes z inst) bytes
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  tls_vec.SecretTlsVecU16.deserialize_bytes_pf inst z hlaw bytes

/-! #### `SecretTlsVecU24`: function and trait-level specs -/

/-- Functional correctness of the trait method of `SecretTlsVecU24` (trait-level post). -/
theorem tls_vec.SecretTlsVecU24.trait_fc {T : Type} (inst : DeserializeBytes T)
    (z : zeroize.Zeroize T) (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
      (tls_vec.SecretTlsVecU24.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes z inst) bytes
    ⦃ ⇓? res => ⌜ (DeserializeBytes.tls_deserialize_bytes.post
        (tls_vec.SecretTlsVecU24.Insts.Tls_codecDeserializeBytes z inst).SizeInst
        (tls_vec.SecretTlsVecU24.Insts.Tls_codecDeserializeBytes z inst) bytes res).holds ⌝ ⦄ :=
  DeserializeBytes.fc_of_char (tls_vec.SecretTlsVecU24.Insts.Tls_codecSize z inst.SizeInst)
    (tls_vec.SecretTlsVecU24.Insts.Tls_codecDeserializeBytes z inst) bytes _
    (tls_vec.SecretTlsVecU24.deserialize_bytes_char inst z hlaw bytes)

/-- The trait method of `SecretTlsVecU24` does not fail. -/
theorem tls_vec.SecretTlsVecU24.trait_pf {T : Type} (inst : DeserializeBytes T)
    (z : zeroize.Zeroize T) (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
      (tls_vec.SecretTlsVecU24.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes z inst) bytes
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  tls_vec.SecretTlsVecU24.deserialize_bytes_pf inst z hlaw bytes

/-! #### `SecretTlsVecU32`: function and trait-level specs -/

/-- Functional correctness of the trait method of `SecretTlsVecU32` (trait-level post). -/
theorem tls_vec.SecretTlsVecU32.trait_fc {T : Type} (inst : DeserializeBytes T)
    (z : zeroize.Zeroize T) (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
      (tls_vec.SecretTlsVecU32.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes z inst) bytes
    ⦃ ⇓? res => ⌜ (DeserializeBytes.tls_deserialize_bytes.post
        (tls_vec.SecretTlsVecU32.Insts.Tls_codecDeserializeBytes z inst).SizeInst
        (tls_vec.SecretTlsVecU32.Insts.Tls_codecDeserializeBytes z inst) bytes res).holds ⌝ ⦄ :=
  DeserializeBytes.fc_of_char (tls_vec.SecretTlsVecU32.Insts.Tls_codecSize z inst.SizeInst)
    (tls_vec.SecretTlsVecU32.Insts.Tls_codecDeserializeBytes z inst) bytes _
    (tls_vec.SecretTlsVecU32.deserialize_bytes_char inst z hlaw bytes)

/-- The trait method of `SecretTlsVecU32` does not fail. -/
theorem tls_vec.SecretTlsVecU32.trait_pf {T : Type} (inst : DeserializeBytes T)
    (z : zeroize.Zeroize T) (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
      (tls_vec.SecretTlsVecU32.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes z inst) bytes
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  tls_vec.SecretTlsVecU32.deserialize_bytes_pf inst z hlaw bytes

/-! #### `Vec<T>` (quic_vec) -/

/-- The size of a slice: the size fold of its elements (from `0`), plus the length prefix
(none above the `2^30 - 1` bound). -/
theorem Shared0Slice.size_rel {T : Type} (S : Size T) (hl : Size.Lawful T S) (s : Slice T) :
    ⦃ ⌜ True ⌝ ⦄ Shared0Slice.Insts.Tls_codecSize.tls_serialized_len S s
    ⦃ ⇓ r => ⌜ ∃ c ll, SizeFoldRel S 0#usize s.val c ∧ r = lenAddVal c ll ∧
        ll.val = (if c.val ≤ 2 ^ 30 - 1 then varint.lenOf c.val else 0) ⌝ ⦄ := by
  have hcall : ∀ c a e n, S.tls_serialized_len e = ok n →
      (quic_vec.SizeShared0Slice.tls_serialized_len.closure.Insts.CoreOpsFunctionFnMutPairUsizeSharedTUsize
        S).call_mut c (a, e) = ok (lenAddVal a n, c) := by
    intro c a e n hn
    simp [quic_vec.SizeShared0Slice.tls_serialized_len.closure.Insts.CoreOpsFunctionFnMutPairUsizeSharedTUsize.call_mut, hn, len_add_ok]
  have hf := size_fold_rel S (Size.lawful_ok S hl) _ hcall
  mvcgen [Shared0Slice.Insts.Tls_codecSize.tls_serialized_len, hf,
    Shared0Slice.size_closure_map_spec, len_add_triple]
  rename_i it hit c hrel rc hrc rm hrm ll hll r
  intro h
  subst hit
  refine ⟨c, ll, hrel, h, ?_⟩
  cases rc with
  | Ok c' =>
    obtain ⟨u, rfl, hul⟩ := hrm.1 c' rfl
    simp only at hll hrc
    subst hll
    rw [if_pos hrc.2, hul, hrc.1]
  | Err e =>
    obtain rfl := hrm.2 e rfl
    simp only at hll hrc
    subst hll
    rw [if_neg (by omega)]
    rfl

/-- The size of a `Vec<T>`: as `Shared0Slice.size_rel`. -/
theorem alloc.vec.Vec.size_rel {T : Type} (S : Size T) (hl : Size.Lawful T S) (v : alloc.vec.Vec T) :
    ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.Insts.Tls_codecSize.tls_serialized_len S v
    ⦃ ⇓ r => ⌜ ∃ c ll, SizeFoldRel S 0#usize v.val c ∧ r = lenAddVal c ll ∧
        ll.val = (if c.val ≤ 2 ^ 30 - 1 then varint.lenOf c.val else 0) ⌝ ⦄ := by
  have h := Shared0Slice.size_rel S hl
  mvcgen [alloc.vec.Vec.Insts.Tls_codecSize.tls_serialized_len, h]
  intro h; subst_vars; exact h

theorem ByteArray_toList_loop (bs : ByteArray) : ∀ (n i : Nat) (r : List UInt8), bs.size - i = n →
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  intro n
  induction n with
  | zero =>
    intro i r h
    rw [ByteArray.toList.loop]
    have : ¬ i < bs.size := by omega
    simp [this]
    omega
  | succ n ih =>
    intro i r h
    rw [ByteArray.toList.loop]
    have hi : i < bs.size := by omega
    simp only [hi, if_true]
    rw [ih (i+1) _ (by omega)]
    have hi' : i < bs.data.toList.length := by simpa using hi
    have hi2 : i < bs.data.size := hi
    have : bs.get! i = bs.data.toList[i] := by
      simp [ByteArray.get!]
      exact getElem!_pos bs.data i hi2
    rw [this]
    simp [List.drop_eq_getElem_cons hi']

theorem ByteArray_toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
  unfold ByteArray.toList
  rw [ByteArray_toList_loop bs bs.size 0 [] (by omega)]
  simp

/-- The bytes of a `toStr` literal are the UTF-8 encoding of some string (so `String::from(&str)`
of a literal has a spec). -/
theorem toStr_utf8 (s : String) (h : s.toByteArray.size ≤ U32.max) :
    ∃ t, alloc.string.String.utf8U8 t = (toStr s h).val := by
  refine ⟨s, ?_⟩
  simp only [alloc.string.String.utf8U8, toStr]
  rw [ByteArray_toList_eq]
  apply List.map_congr_left
  intro b _
  apply UScalar.eq_of_val_eq
  simp

theorem alloc.vec.Vec.deserialize_bytes_loop_body_char {T : Type} (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (length : Std.Usize) (N : Nat) (hN : N ≤ Usize.max)
    (result : alloc.vec.Vec T) (remainder : Slice Std.U8) (read : Std.Usize)
    (hinv : DesLoopInv inst.SizeInst 0#usize N result.val remainder read) :
    ⦃ ⌜ True ⌝ ⦄
    alloc.vec.Vec.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes_loop.body inst length remainder
      result read
    ⦃ ⇓ r => ⌜ match r with
      | .done (rem, res, rd, fl) => fl = core.option.Option.None →
          (∃ s, SizeFoldRel inst.SizeInst 0#usize res.val s ∧ s.val + rem.val.length = N) ∧
          rd.val + rem.val.length = N
      | .cont (rem, res, rd) => DesLoopInv inst.SizeInst 0#usize N res.val rem rd ∧
          rem.val.length < remainder.val.length ⌝ ⦄ := by
  have hd := fun b => hlaw.tls_deserialize_bytes_spec b (pre_holds_of_ok_true rfl)
  obtain ⟨hres, ⟨s, hs, hsN⟩, hr⟩ := hinv
  mvcgen [alloc.vec.Vec.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes_loop.body, hd,
    core.convert.Into.Blanket.into]
  case vc1.h =>
    rename_i hlt r p hx hpost r2 h2 r1 h1 r0 ha hb
    scalar_tac
  case vc2.h => exact toStr_utf8 _ _
  case vc3 => intro h; cases h
  case vc4.hQ =>
    rename_i hlt r p hx hpost r2 h2 r1 h1 r0 ha hb res hnz hpush rd hrd
    obtain ⟨e, nxt⟩ := p
    obtain ⟨n, hn, hl⟩ := DeserializeBytes.post_ok_elim _ _ _ _ _ hpost
    subst h2 h1
    have l1 := Slice.len_val remainder
    have l2 := Slice.len_val nxt
    simp only [Slice.length] at l1 l2
    have hnz' : r0.val ≠ 0 := fun h => hnz (UScalar.eq_of_val_eq (by simpa using h))
    have hr0 : r0.val = n.val := by dsimp only at *; omega
    have hsn : (lenAddVal s n).val = s.val + n.val := lenAddVal_val s n (by dsimp only at *; omega)
    refine ⟨⟨?_, ⟨lenAddVal s n, ?_, ?_⟩, ?_⟩, ?_⟩
    · rw [hpush]; simp; dsimp only at *; omega
    · rw [hpush]; exact hs.snoc e n hn
    · dsimp only at *; omega
    · dsimp only at *; omega
    · dsimp only at *; omega
  case vc5.h_fail =>
    exfalso
    rename_i hlt r p hx hpost r2 h2 r1 h1 r0 ha hb res hnz hpush hbig
    obtain ⟨e, nxt⟩ := p
    obtain ⟨n, hn, hl⟩ := DeserializeBytes.post_ok_elim _ _ _ _ _ hpost
    subst h2 h1
    have l1 := Slice.len_val remainder
    have l2 := Slice.len_val nxt
    simp only [Slice.length] at l1 l2
    dsimp only at *
    scalar_tac
  case vc6.h_fail =>
    exfalso
    rename_i hlt r p hx hpost r2 h2 r1 h1 hlt2
    obtain ⟨e, nxt⟩ := p
    obtain ⟨n, hn, hl⟩ := DeserializeBytes.post_ok_elim _ _ _ _ _ hpost
    subst h2 h1
    have l1 := Slice.len_val remainder
    have l2 := Slice.len_val nxt
    simp only [Slice.length] at l1 l2
    dsimp only at *
    scalar_tac
  case vc7 => intro h; cases h
  case vc8.hQ => exact ⟨⟨s, hs, hsN⟩, by simpa using hr⟩

theorem alloc.vec.Vec.deserialize_bytes_loop_char {T : Type} (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (length : Std.Usize) (N : Nat) (hN : N ≤ Usize.max)
    (result : alloc.vec.Vec T) (remainder : Slice Std.U8) (read : Std.Usize)
    (hinv : DesLoopInv inst.SizeInst 0#usize N result.val remainder read) :
    ⦃ ⌜ True ⌝ ⦄
    alloc.vec.Vec.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes_loop inst remainder length
      result read
    ⦃ ⇓ r => ⌜ r.2.2.2 = core.option.Option.None →
        (∃ s, SizeFoldRel inst.SizeInst 0#usize r.2.1.val s ∧ s.val + r.1.val.length = N) ∧
        r.2.2.1.val + r.1.val.length = N ⌝ ⦄ := by
  unfold alloc.vec.Vec.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes_loop
  apply Aeneas.Std.WP.spec_to_mvcgen
  apply Aeneas.Std.loop.spec_decr_nat
    (fun p : Slice Std.U8 × alloc.vec.Vec T × Std.Usize => p.1.val.length)
    (fun p => DesLoopInv inst.SizeInst 0#usize N p.2.1.val p.1 p.2.2)
  · rintro ⟨rem, res, rd⟩ h
    obtain ⟨v, hv, hP⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp
      (alloc.vec.Vec.deserialize_bytes_loop_body_char inst hlaw length N hN res rem rd h)
    dsimp only
    rw [hv]
    refine (Aeneas.Std.WP.spec_ok v).mpr ?_
    cases v with
    | done y => exact hP
    | cont x => exact hP
  · exact hinv

/-- The size of a `Vec<T>` whose size fold is `c` (when the sum does not overflow). -/
theorem alloc.vec.Vec.size_ok {T : Type} (S : Size T) (hl : Size.Lawful T S) (v : alloc.vec.Vec T)
    (c : Std.Usize) (hrel : SizeFoldRel S 0#usize v.val c)
    (hc : c.val + (if c.val ≤ 2 ^ 30 - 1 then varint.lenOf c.val else 0) ≤ Usize.max) :
    ∃ n, alloc.vec.Vec.Insts.Tls_codecSize.tls_serialized_len S v = ok n ∧
      n.val = c.val + (if c.val ≤ 2 ^ 30 - 1 then varint.lenOf c.val else 0) := by
  obtain ⟨r, hr, c', ll, hrel', hr', hll⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp
    (alloc.vec.Vec.size_rel S hl v)
  have := hrel.functional hrel'
  subst this
  refine ⟨r, hr, ?_⟩
  rw [hr', lenAddVal_val _ _ (by rw [hll]; exact hc), hll]

/-- `Vec<T>::tls_deserialize_bytes` from the trait contract of `T`. -/
theorem alloc.vec.Vec.deserialize_bytes_char {T : Type} (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes inst bytes
    ⦃ ⇓ r => ⌜ ∀ v rem, r = .Ok (v, rem) → ∃ n,
        alloc.vec.Vec.Insts.Tls_codecSize.tls_serialized_len inst.SizeInst v = ok n ∧
        rem.val.length + n.val = bytes.val.length ⌝ ⦄ := by
  have hl := fun (result : alloc.vec.Vec T) (remainder : Slice Std.U8) (length read : Std.Usize)
      (hinv : DesLoopInv inst.SizeInst 0#usize remainder.val.length result.val remainder read) =>
    alloc.vec.Vec.deserialize_bytes_loop_char inst hlaw length remainder.val.length
      (by have := remainder.property; scalar_tac) result remainder read hinv
  mvcgen [alloc.vec.Vec.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes,
    quic_vec.ContentLength.deserialize_char, varint.TlsVarInt.value, hl,
    alloc.vec.Vec.new_spec, core.hint.must_use_spec]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  all_goals (try (intro _ _ h; cases h; done))
  all_goals (try (intros; simp [PostCond.ok]; done))
  all_goals (try (exfalso; simp_all; done))
  case vc1 =>
    rename_i r0 hP r1 p hx r2 htf r3 val hx2 hv0 rv hrv hr0 hr2
    intro v rem h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (core.result.Result.Ok.inj h)
    have hp := hP p.1 p.2 hr0
    have hy := htf.1 val hr2
    have hv : val.val = 0 := by rw [hv0]; rfl
    have hrel : SizeFoldRel inst.SizeInst 0#usize rv.val 0#usize := by
      rw [hrv]; simp [Slice.new]; exact .nil _
    obtain ⟨n, hn, hnv⟩ := alloc.vec.Vec.size_ok inst.SizeInst hlaw.SizeInstLawful rv 0#usize hrel
      (by simp [varint.lenOf]; scalar_tac)
    refine ⟨n, hn, ?_⟩
    have h0 : varint.lenOf 0 = 1 := by simp [varint.lenOf]
    simp [h0] at hnv
    have := hp.2
    rw [show p.1.val = 0 by omega, h0] at this
    omega
  case vc2.hinv =>
    rename_i r0 hP r1 p hx r2 htf r3 val hx2 hv0 rv hrv hr0 hr2
    refine ⟨by simp [hrv, Slice.new], ⟨0#usize, ?_, by simp⟩, by simp⟩
    rw [hrv]; simp [Slice.new]; exact .nil _
  case vc4 =>
    rename_i r0 hP r1 p hx r2 htf r3 val hx2 hnz rv hrv res hnone hne hpost hr0 hr2
    intro v rem h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (core.result.Result.Ok.inj h)
    have hp := hP p.1 p.2 hr0
    have hy := htf.1 val hr2
    obtain ⟨⟨s, hs, hsN⟩, hrd⟩ := hpost hnone
    have hrv' : res.2.2.1.val = val.val := by simpa using hne
    have hsv : s.val = p.1.val := by
      rw [hrv'] at hrd
      omega
    have hb : bytes.val.length ≤ Usize.max := by have := bytes.property; scalar_tac
    have hle : p.1.val ≤ 2 ^ 30 - 1 := hp.1
    obtain ⟨n, hn, hnv⟩ := alloc.vec.Vec.size_ok inst.SizeInst hlaw.SizeInstLawful res.2.1 s hs
      (by rw [if_pos (by omega), hsv]; have := hp.2; omega)
    refine ⟨n, hn, ?_⟩
    rw [if_pos (by omega), hsv] at hnv
    have := hp.2
    omega

/-- The trait method of `Vec<T>` does not fail. -/
theorem alloc.vec.Vec.trait_pf {T : Type} (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
      (alloc.vec.Vec.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes inst) bytes
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  obtain ⟨v, hv, _⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp
    (alloc.vec.Vec.deserialize_bytes_char inst hlaw bytes)
  rw [hv]
  apply RustM.ok_spec
  trivial

/-- Functional correctness of the trait method of `Vec<T>` (trait-level post). -/
theorem alloc.vec.Vec.trait_fc {T : Type} (inst : DeserializeBytes T)
    (hlaw : DeserializeBytes.Lawful T inst) (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄
      (alloc.vec.Vec.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes inst) bytes
    ⦃ ⇓? res => ⌜ (DeserializeBytes.tls_deserialize_bytes.post
        (alloc.vec.Vec.Insts.Tls_codecDeserializeBytes inst).SizeInst
        (alloc.vec.Vec.Insts.Tls_codecDeserializeBytes inst) bytes res).holds ⌝ ⦄ :=
  DeserializeBytes.fc_of_char (alloc.vec.Vec.Insts.Tls_codecSize inst.SizeInst)
    (alloc.vec.Vec.Insts.Tls_codecDeserializeBytes inst) bytes _
    (alloc.vec.Vec.deserialize_bytes_char inst hlaw bytes)


/-! ### `Slice::to_vec` with a non-failing `clone` -/

/-- `to_vec` does not fail when `clone` does not, and preserves the length. -/
theorem alloc.slice.Slice.to_vec_len {T : Type} (inst : core.clone.Clone T)
    (hc : ∀ x, ⦃ ⌜ True ⌝ ⦄ inst.clone x ⦃ ⇓ _ => ⌜ True ⌝ ⦄) (s : Slice T) :
    ⦃ ⌜ True ⌝ ⦄ alloc.slice.Slice.to_vec inst s
    ⦃ ⇓ r => ⌜ (r : Slice T).val.length = s.val.length ⌝ ⦄ := by
  have mapM_ok : ∀ l : List T, ∃ l', l.mapM inst.clone = .ok l' ∧ l'.length = l.length := by
    intro l
    induction l with
    | nil => exact ⟨[], rfl, rfl⟩
    | cons x xs ih =>
      obtain ⟨y, hy⟩ := triple_true_ok (hc x)
      obtain ⟨l', hl', hlen⟩ := ih
      refine ⟨y :: l', ?_, by simp [hlen]⟩
      simp [List.mapM_cons, hy, hl']; rfl
  have hlen : s.val.length ≤ Usize.max := s.property
  obtain ⟨l', hl', hlen'⟩ := mapM_ok s.val
  unfold alloc.slice.Slice.to_vec alloc.slice.Dummy.to_vec
  simp [rust_primitives.sequence.seq_empty, rust_primitives.sequence.seq_extend, alloc.vec.from_seq,
    Slice.new, hl']
  rw [dif_pos (by omega)]
  mvcgen


/-! ### Generic slice serializer: partial characterization

An `Ok` result of the `Slice` serializer has the size given by `tls_serialized_len` (partial
statement; panic freedom is `Shared0Slice.serialize_pf`). -/

/-- Partial-correctness spec of `loop`: an invariant `inv` preserved by every step, and its `done`
values satisfy `Q`. -/
theorem loop_partial_spec {α β : Type} (body : α → RustM (ControlFlow α β)) (init : α)
    (inv : α → Prop) (Q : β → Prop) (hinit : inv init)
    (hbody : ∀ x, inv x → ⦃ ⌜ True ⌝ ⦄ body x
      ⦃ ⇓? cf => ⌜ match cf with | .cont r => inv r | .done y => Q y ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄ loop body init ⦃ ⇓? y => ⌜ Q y ⌝ ⦄ := by
  refine Aeneas.Std.loop_spec (γ := Unit) inv (fun _ _ => False) (fun _ => ()) ⟨fun _ => ⟨_, by simp⟩⟩
    hinit ?_
  intro x hx
  have := hbody x hx
  cases hb : body x <;> rw [hb] at this <;>
    simp_all [Triple, PostCond.mayThrow, PostCond.okAssertion, PostCond.failAssertion,
      PostCond.divAssertion, PostCond.div, WP.wp, PredTrans.apply] <;> (try split) <;> simp_all

/-- Weakening the post of a partial triple. -/
theorem partial_triple_post_mono {α : Type} {x : RustM α} {P Q : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓? r => ⌜ P r ⌝ ⦄) (hPQ : ∀ r, P r → Q r) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓? r => ⌜ Q r ⌝ ⦄ :=
  partial_triple_of_ok fun _ hr => hPQ _ (ok_of_partial_triple h hr)

/-- Exact sums of the element sizes (as naturals). -/
inductive SizeNat {T : Type} (S : Size T) : List T → Nat → Prop
  | nil : SizeNat S [] 0
  | cons (x : T) (l : List T) (n : Std.Usize) (N : Nat) :
      S.tls_serialized_len x = ok n → SizeNat S l N → SizeNat S (x :: l) (n.val + N)

theorem SizeNat.snoc {T : Type} {S : Size T} {l : List T} {N : Nat} (h : SizeNat S l N)
    (e : T) (n : Std.Usize) (hn : S.tls_serialized_len e = ok n) :
    SizeNat S (l ++ [e]) (N + n.val) := by
  induction h with
  | nil => simpa using SizeNat.cons e [] n 0 hn .nil
  | cons x l n' N' hx _ ih =>
    have := SizeNat.cons x _ n' _ hx ih
    rwa [show n'.val + (N' + n.val) = n'.val + N' + n.val by omega] at this

theorem SizeNat.head {T : Type} {S : Size T} {l : List T} {N : Nat} (h : SizeNat S l N)
    (hl : 0 < l.length) :
    ∃ (n : Std.Usize) (N' : Nat), S.tls_serialized_len (l.get ⟨0, hl⟩) = ok n ∧ N = n.val + N' := by
  cases h with
  | nil => exact absurd hl (by simp)
  | cons x l' n N' hx _ => exact ⟨n, N', hx, rfl⟩

/-- The folds are the exact sum when it fits. -/
theorem SizeFoldRel.val_eq {T : Type} {S : Size T} {a : Std.Usize} {l : List T} {r : Std.Usize}
    (h : SizeFoldRel S a l r) {N : Nat} (hN : SizeNat S l N) (hle : a.val + N ≤ Usize.max) :
    r.val = a.val + N := by
  induction h generalizing N with
  | nil a => cases hN; simp
  | cons a x l n r hx _ ih =>
    rcases hN with _ | ⟨_, _, n2, N2, hx2, hN2⟩
    · rw [hx] at hx2
      have hnn : n2 = n := (ok.inj hx2).symm
      subst hnn
      have := lenAddVal_val a n2 (by omega)
      rw [ih hN2 (by omega), this]
      omega

/-- A loop whose result is not tracked. -/
theorem loop_trivial_partial {α β : Type} (body : α → RustM (ControlFlow α β)) (x : α) :
    ⦃ ⌜ True ⌝ ⦄ loop body x ⦃ ⇓? _ => ⌜ True ⌝ ⦄ :=
  partial_triple_of_ok fun _ _ => trivial

/-- Partial spec of the serialisation loop of the slice serializer: if it finishes without error,
the output grew by the sum of the element sizes. -/
theorem loop_ser_partial_spec {T : Type} (S : Size T) (it : core.slice.iter.Iter T)
    (out : alloc.vec.Vec Std.U8)
    (body : core.slice.iter.Iter T × alloc.vec.Vec Std.U8 →
      RustM (ControlFlow (core.slice.iter.Iter T × alloc.vec.Vec Std.U8)
        (alloc.vec.Vec Std.U8 × core.option.Option Error)))
    (hbody : ∀ (it' : core.slice.iter.Iter T) (o : alloc.vec.Vec Std.U8),
      ⦃ ⌜ True ⌝ ⦄ body (it', o)
      ⦃ ⇓? r => ⌜ match r with
        | .done y => y.2 = core.option.Option.None → (it' : Slice T).val = [] ∧ y.1 = o
        | .cont p => ∃ e n, (it' : Slice T).val = e :: (p.1 : Slice T).val ∧
            S.tls_serialized_len e = ok n ∧
            (p.2 : Slice Std.U8).val.length = (o : Slice Std.U8).val.length + n.val ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄ loop body (it, out)
    ⦃ ⇓? r => ⌜ r.2 = core.option.Option.None → ∃ N, SizeNat S (it : Slice T).val N ∧
        (r.1 : Slice Std.U8).val.length = (out : Slice Std.U8).val.length + N ⌝ ⦄ := by
  refine loop_partial_spec body (it, out)
    (fun p => ∃ lc N0, (it : Slice T).val = lc ++ (p.1 : Slice T).val ∧ SizeNat S lc N0 ∧
      (p.2 : Slice Std.U8).val.length = (out : Slice Std.U8).val.length + N0)
    _ ⟨[], 0, by simp, .nil, by simp⟩ ?_
  rintro ⟨it', o⟩ ⟨lc, N0, h1, h2, h3⟩
  apply partial_triple_post_mono (hbody it' o)
  intro r hr
  cases r with
  | done y =>
    intro hy
    obtain ⟨h0, rfl⟩ := hr hy
    refine ⟨N0, ?_, h3⟩
    simp only at h1 h0 ⊢
    rw [h1, h0, List.append_nil]; exact h2
  | cont p =>
    obtain ⟨e, n, hl, hn, hp⟩ := hr
    refine ⟨lc ++ [e], N0 + n.val, ?_, h2.snoc e n hn, ?_⟩
    · rw [h1, hl]; simp
    · rw [hp]; simp only at h3; omega


/-- Total spec of `loop`: an invariant `inv` preserved by every step with a decreasing measure `μ`,
and its `done` values satisfy `Q`. -/
theorem loop_total_spec {α β : Type} (body : α → RustM (ControlFlow α β)) (init : α)
    (inv : α → Prop) (μ : α → Nat) (Q : β → Prop) (hinit : inv init)
    (hbody : ∀ x, inv x → ⦃ ⌜ True ⌝ ⦄ body x
      ⦃ ⇓ cf => ⌜ match cf with | .cont r => inv r ∧ μ r < μ x | .done y => Q y ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄ loop body init ⦃ ⇓ y => ⌜ Q y ⌝ ⦄ := by
  apply Aeneas.Std.WP.spec_to_mvcgen
  refine Aeneas.Std.loop.spec_decr_nat μ inv Q body init (fun x hx => ?_) hinit
  obtain ⟨r, hr, hP⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp (hbody x hx)
  rw [hr, Aeneas.Std.WP.spec_ok]
  cases r <;> exact hP

/-- Total spec of the sizing loop of the slice serializer: it does not fail, and an `Ok` result is the
exact sum of the element sizes. -/
theorem loop_sum_total {T : Type} (S : Size T) (it : core.slice.iter.Iter T) (acc : Std.Usize)
    (body : core.slice.iter.Iter T × Std.Usize →
      RustM (ControlFlow (core.slice.iter.Iter T × Std.Usize) (core.result.Result Std.Usize Error)))
    (hbody : ∀ (it' : core.slice.iter.Iter T) (a : Std.Usize),
      ⦃ ⌜ True ⌝ ⦄ body (it', a)
      ⦃ ⇓ r => ⌜ match r with
        | .done y => ∀ c, y = .Ok c → (it' : Slice T).val = [] ∧ c = a
        | .cont p => ∃ e n, (it' : Slice T).val = e :: (p.1 : Slice T).val ∧
            S.tls_serialized_len e = ok n ∧ p.2.val = a.val + n.val ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄ loop body (it, acc)
    ⦃ ⇓ r => ⌜ ∀ c, r = .Ok c → ∃ N, SizeNat S (it : Slice T).val N ∧ c.val = acc.val + N ⌝ ⦄ := by
  refine loop_total_spec body (it, acc)
    (fun p => ∃ lc N0, (it : Slice T).val = lc ++ (p.1 : Slice T).val ∧ SizeNat S lc N0 ∧
      p.2.val = acc.val + N0)
    (fun p => (p.1 : Slice T).val.length) _ ⟨[], 0, by simp, .nil, by simp⟩ ?_
  rintro ⟨it', a⟩ ⟨lc, N0, h1, h2, h3⟩
  apply triple_post_mono (hbody it' a)
  intro r hr
  cases r with
  | done y =>
    intro c hy
    obtain ⟨h0, rfl⟩ := hr c hy
    simp only at h1 h0 h3
    exact ⟨N0, by rw [h1, h0, List.append_nil]; exact h2, h3⟩
  | cont p =>
    obtain ⟨e, n, hl, hn, hp⟩ := hr
    refine ⟨⟨lc ++ [e], N0 + n.val, ?_, h2.snoc e n hn, ?_⟩, ?_⟩
    · rw [h1, hl]; simp
    · simp only at h3; omega
    · simp [hl]

/-- Total spec of the serialisation loop of the slice serializer: it does not fail, as long as the
total size of the remaining elements still fits in the vector; the output does not shrink. -/
theorem loop_append_total {T : Type} (S : Size T) (it : core.slice.iter.Iter T)
    (out : alloc.vec.Vec Std.U8)
    (body : core.slice.iter.Iter T × alloc.vec.Vec Std.U8 →
      RustM (ControlFlow (core.slice.iter.Iter T × alloc.vec.Vec Std.U8)
        (alloc.vec.Vec Std.U8 × core.option.Option Error)))
    (hinit : ∃ N, SizeNat S (it : Slice T).val N ∧ (out : Slice Std.U8).val.length + N ≤ Usize.max)
    (hbody : ∀ (it' : core.slice.iter.Iter T) (o : alloc.vec.Vec Std.U8),
      (∃ N, SizeNat S (it' : Slice T).val N ∧ (o : Slice Std.U8).val.length + N ≤ Usize.max) →
      ⦃ ⌜ True ⌝ ⦄ body (it', o)
      ⦃ ⇓ r => ⌜ match r with
        | .done y => (o : Slice Std.U8).val.length ≤ (y.1 : Slice Std.U8).val.length
        | .cont p => ∃ e n, (it' : Slice T).val = e :: (p.1 : Slice T).val ∧
            S.tls_serialized_len e = ok n ∧
            (p.2 : Slice Std.U8).val.length = (o : Slice Std.U8).val.length + n.val ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄ loop body (it, out)
    ⦃ ⇓ r => ⌜ (out : Slice Std.U8).val.length ≤ (r.1 : Slice Std.U8).val.length ⌝ ⦄ := by
  refine loop_total_spec body (it, out)
    (fun p => (∃ N, SizeNat S (p.1 : Slice T).val N ∧
        (p.2 : Slice Std.U8).val.length + N ≤ Usize.max) ∧
      (out : Slice Std.U8).val.length ≤ (p.2 : Slice Std.U8).val.length)
    (fun p => (p.1 : Slice T).val.length) _ ⟨hinit, le_refl _⟩ ?_
  rintro ⟨it', o⟩ ⟨hinv, hle⟩
  apply triple_post_mono (hbody it' o hinv)
  intro r hr
  cases r with
  | done y => exact le_trans hle hr
  | cont p =>
    obtain ⟨e, n, hl, hn, hp⟩ := hr
    obtain ⟨N, hN, hle'⟩ := hinv
    simp only at hN hle hle' ⊢
    rw [hl] at hN
    obtain _ | ⟨_, _, n2, N2, hx2, hN2⟩ := hN
    have := ok.inj (hn.symm.trans hx2)
    subst this
    exact ⟨⟨⟨N2, hN2, by omega⟩, by omega⟩, by simp [hl]⟩

theorem list_cons_get_drop {α : Type} (l : List α) (h : 0 < l.length) :
    l = l.get ⟨0, h⟩ :: l.drop 1 := by
  cases l with
  | nil => exact absurd h (Nat.lt_irrefl _)
  | cons x xs => rfl

/-- The element serializer of a lawful `SerializeBytes` instance does not panic and meets its size
contract (as a spec for `mvcgen`). -/
theorem SerializeBytes.elem_char {T : Type} (inst : SerializeBytes T)
    (hlaw : SerializeBytes.Lawful T inst) (x : T) :
    ⦃ ⌜ True ⌝ ⦄ inst.tls_serialize_bytes x
    ⦃ ⇓ r => ⌜ ∀ b, r = .Ok b → ∃ n, inst.SizeInst.tls_serialized_len x = ok n ∧
      (b : Slice Std.U8).val.length = n.val ⌝ ⦄ := by
  obtain ⟨a, ha, hP⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp
    (hlaw.tls_serialize_bytes_spec x (pre_holds_of_ok_true rfl))
  rw [ha]
  apply RustM.ok_spec
  intro b hb
  subst hb
  exact SerializeBytes.post_ok_elim _ _ _ _ hP

/-- The element serializer of a lawful `SerializeBytes` instance meets its size contract
(partial form, as a spec for `mvcgen`). -/
theorem SerializeBytes.elem_partial {T : Type} (inst : SerializeBytes T)
    (hlaw : SerializeBytes.Lawful T inst) (x : T) :
    ⦃ ⌜ True ⌝ ⦄ inst.tls_serialize_bytes x
    ⦃ ⇓? r => ⌜ ∀ b, r = .Ok b → ∃ n, inst.SizeInst.tls_serialized_len x = ok n ∧
      (b : Slice Std.U8).val.length = n.val ⌝ ⦄ :=
  partial_of_total (SerializeBytes.elem_char inst hlaw x)

/-- Unfold the hand-translated slice serializer, with the copies of the crate functions it calls
folded back to the originals (so that their specs apply). -/
macro "ser_slice_setup" : tactic => `(tactic| (
  unfold Shared0Slice.Insts.Tls_codecSerializeBytes.tls_serialize_bytes
  nth_rewrite 1 [slice_iter_ok]
  erw [bind_tc_ok]
  simp only [Copied.varint.TlsVarInt.bytes_len_eq, Copied.varint.TlsVarInt.write_bytes_eq,
    Copied.checked_alloc_len_eq, Copied.quic_vec.ContentLength.from_usize_eq]))

/-- `mvcgen` on the unfolded slice serializer, with the specs of the functions it calls; the
argument lists the specs of the two loops and of the element functions. -/
syntax "ser_slice_mvcgen" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| ser_slice_mvcgen [$ts,*]) => `(tactic| mvcgen [-Aeneas.Std.loop_spec, $ts,*,
    quic_vec.ContentLength.from_usize_spec, varint.TlsVarInt.bytes_len_spec,
    checked_alloc_len_ok, alloc.vec.Vec.with_capacity, alloc.vec.Vec.resize_U8_len_spec,
    alloc.vec.Vec.Insts.CoreOpsDerefDerefMutSlice.deref_mut, alloc.vec.Vec.as_mut_slice,
    rust_primitives.sequence.seq_to_slice_mut, varint.TlsVarInt.write_bytes_spec,
    core.slice.Slice.iter, core.iter.traits.collect.IntoIterator.Blanket.into_iter,
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
    alloc.vec.Vec.append, rust_primitives.sequence.seq_concat])

/-- The `<&[T]>::tls_serialize_bytes` of the trait contracts of `T`: an `Ok out` has the length given
by `tls_serialized_len` (partial form, see `Shared0Slice.serialize_pf`). -/
theorem Shared0Slice.serialize_partial {T : Type} (inst : SerializeBytes T)
    (hlaw : SerializeBytes.Lawful T inst) (s : Slice T) :
    ⦃ ⌜ True ⌝ ⦄ Shared0Slice.Insts.Tls_codecSerializeBytes.tls_serialize_bytes inst s
    ⦃ ⇓? r => ⌜ ∀ out, r = .Ok out → ∃ n,
        Shared0Slice.Insts.Tls_codecSize.tls_serialized_len inst.SizeInst s = ok n ∧
        (out : Slice Std.U8).val.length = n.val ⌝ ⦄ := by
  have hs := SerializeBytes.elem_partial inst hlaw
  obtain ⟨n, hn, c', ll', hrel', hnv, hll'⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp
    (Shared0Slice.size_rel inst.SizeInst hlaw.SizeInstLawful s)
  ser_slice_setup
  have hsum := loop_trivial_partial
    (α := core.slice.iter.Iter T × Std.Usize) (β := core.result.Result Std.Usize Error)
  have hser := @loop_ser_partial_spec T inst.SizeInst
  ser_slice_mvcgen [hsum, hser, hs]
  all_goals (try clear hsum hser)
  try_vcs
  all_goals (try (intros; simp [PostCond.ok]; done))
  · rw [← List.length_eq_zero_iff]
    scalar_tac
  · rename_i _ _ _ bytes _ hb comb hc
    obtain ⟨n, hn, hl⟩ := hb bytes rfl
    refine ⟨_, n, ?_, hn, ?_⟩
    · simp only [show (0#usize).val = 0 from rfl, List.take_zero, List.nil_append, zero_add]
      exact list_cons_get_drop _ ‹_›
    · simp [comb, hl]
  · intro h
    cases h
  · intro out h
    cases h
  · intro out h
    cases h
  · rename_i _ _ c _ _ _ hfrom _ val _ hcf1 ll hbl _ hchk _ _ _ _ _ _ _ hout1 back r3 hw _ _ _ _ r4 hnone hrel
      i3 hi3 i4 hi4 hge hne
    intro out hout
    obtain rfl := core.result.Result.Ok.inj hout
    simp only [continue_eq_tryCF] at hcf1
    subst hcf1
    simp only at hfrom
    obtain ⟨N, hN, hlen⟩ := hrel hnone
    have hc := varint.lenOf_char _ _ hbl
    have hw2 := (hw.2 (by omega)).2
    have hback : (back r3.2 : Slice Std.U8).val.length = (r3.2 : Slice Std.U8).val.length := rfl
    have h0 : (0#usize).val = 0 := rfl
    have hi3v : i3.val = (r4.1 : Slice Std.U8).val.length := by rw [hi3]; simp
    have hi4v : i4.val = i3.val - ll.val := hi4
    have hcv : i4.val = c.val := by simpa using hne
    have hbound : (r4.1 : Slice Std.U8).val.length ≤ Usize.max := (r4.1 : Slice Std.U8).property
    have hcN : c.val = N := by omega
    have hc' := hrel'.val_eq hN (by omega)
    have hll'v : ll'.val = varint.lenOf N := by
      rw [hll', if_pos (by omega)]
      congr 1
      omega
    have hllv : ll.val = varint.lenOf N := by rw [hc.1]; congr 1; omega
    refine ⟨n, hn, ?_⟩
    rw [hnv, lenAddVal_val _ _ (by omega)]
    omega


/-- The `<&[T]>::tls_serialize_bytes` of the trait contracts of `T` does not fail. -/
theorem Shared0Slice.serialize_pf {T : Type} (inst : SerializeBytes T)
    (hlaw : SerializeBytes.Lawful T inst) (s : Slice T) :
    ⦃ ⌜ True ⌝ ⦄ Shared0Slice.Insts.Tls_codecSerializeBytes.tls_serialize_bytes inst s
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  have hs := SerializeBytes.elem_char inst hlaw
  have hz := Size.len_char inst.SizeInst hlaw.SizeInstLawful
  have hsum := @loop_sum_total T inst.SizeInst
  have happ := @loop_append_total T inst.SizeInst
  ser_slice_setup
  ser_slice_mvcgen [hsum, happ, hs, hz, checked_len_add_triple]
  all_goals (try clear hsum happ hs hz)
  try_vcs
  all_goals (try exact ‹core.ops.control_flow.ControlFlow.Break _ = tryCF _›)
  all_goals (try (intros; simp [PostCond.ok]; done))
  · rintro c ⟨⟩
    exact ⟨by rw [← List.length_eq_zero_iff]; scalar_tac, rfl⟩
  · simp only [continue_eq_tryCF] at *
    subst_vars
    exact ⟨_, _, by simpa using list_cons_get_drop _ ‹_›, ‹_›, (checkedLenAddRes_ok _ _ _ ‹_›).1⟩
  · intro h; subst h; simp [PostCond.ok]; mvcgen; simp
  · exfalso; scalar_tac
  · simp only [continue_eq_tryCF] at *
    subst_vars
    have hc := varint.lenOf_char _ _ ‹1 ≤ _ ∧ _›
    simp only [core.result.Result.Ok.injEq, forall_eq, forall_eq'] at *
    obtain ⟨N, hN, hv⟩ := ‹∃ N, _›
    obtain ⟨-, hl⟩ := ‹(_ < _ → _) ∧ (_ ≤ _ → _)›
    have hl := (hl (by omega)).2
    exact ⟨N, hN, by dsimp +zetaDelta only; scalar_tac⟩
  · simp only [core.result.Result.Ok.injEq, forall_eq'] at *
    obtain ⟨n, hn, hl⟩ := ‹∃ n, _›
    exact ⟨_, n, by simpa using list_cons_get_drop _ ‹_›, hn, by simp +zetaDelta [hl]⟩
  · exfalso
    obtain ⟨N, hN, hle⟩ := ‹∃ N, _›
    obtain ⟨n, N', hx, rfl⟩ := hN.head (by scalar_tac)
    simp only [core.result.Result.Ok.injEq, forall_eq'] at *
    obtain ⟨n2, hn2, hlen⟩ := ‹∃ n, _›
    obtain rfl := ok.inj (hx.symm.trans hn2)
    simp +zetaDelta [List.length_append] at *
    omega
  · exfalso; scalar_tac
  · exfalso
    have hc := varint.lenOf_char _ _ ‹1 ≤ _ ∧ _›
    obtain ⟨-, hl⟩ := ‹(_ < _ → _) ∧ (_ ≤ _ → _)›
    have hl := (hl (by omega)).2
    dsimp +zetaDelta only at *
    scalar_tac

theorem alloc.vec.Vec.as_slice_ok {T : Type} (v : alloc.vec.Vec T) :
    alloc.vec.Vec.as_slice v = ok (v : Slice T) := by
  obtain ⟨a, ha, hP⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp (alloc.vec.Vec.as_slice_spec v)
  rw [ha, hP]
  rfl

/-- The `Vec<T>` size is the size of its slice. -/
theorem alloc.vec.Vec.size_eq_slice {T : Type} (S : Size T) (v : alloc.vec.Vec T) :
    alloc.vec.Vec.Insts.Tls_codecSize.tls_serialized_len S v =
      Shared0Slice.Insts.Tls_codecSize.tls_serialized_len S (v : Slice T) := by
  unfold alloc.vec.Vec.Insts.Tls_codecSize.tls_serialized_len
  rw [alloc.vec.Vec.as_slice_ok]
  rfl

theorem Shared0Vec.size_eq_slice {T : Type} (S : Size T) (v : alloc.vec.Vec T) :
    Shared0Vec.Insts.Tls_codecSize.tls_serialized_len S v =
      Shared0Slice.Insts.Tls_codecSize.tls_serialized_len S (v : Slice T) := by
  unfold Shared0Vec.Insts.Tls_codecSize.tls_serialized_len
  rw [alloc.vec.Vec.size_eq_slice]

/-- The `&Vec<T>` serializer is the slice serializer of its slice. -/
theorem Shared0Vec.ser_eq_slice {T : Type} (inst : SerializeBytes T) (v : alloc.vec.Vec T) :
    Shared0Vec.Insts.Tls_codecSerializeBytes.tls_serialize_bytes inst v =
      Shared0Slice.Insts.Tls_codecSerializeBytes.tls_serialize_bytes inst (v : Slice T) := by
  unfold Shared0Vec.Insts.Tls_codecSerializeBytes.tls_serialize_bytes
  rw [alloc.vec.Vec.as_slice_ok]
  erw [bind_tc_ok]

/-- The `Vec<T>` serializer is the slice serializer of its slice. -/
theorem alloc.vec.Vec.ser_eq_slice {T : Type} (inst : SerializeBytes T) (v : alloc.vec.Vec T) :
    alloc.vec.Vec.Insts.Tls_codecSerializeBytes.tls_serialize_bytes inst v =
      Shared0Slice.Insts.Tls_codecSerializeBytes.tls_serialize_bytes inst (v : Slice T) := by
  unfold alloc.vec.Vec.Insts.Tls_codecSerializeBytes.tls_serialize_bytes
  rw [alloc.vec.Vec.as_slice_ok]
  erw [bind_tc_ok]

/-- The `&Vec<T>` serializer does not fail. -/
theorem Shared0Vec.serialize_pf {T : Type} (inst : SerializeBytes T)
    (hlaw : SerializeBytes.Lawful T inst) (v : alloc.vec.Vec T) :
    ⦃ ⌜ True ⌝ ⦄ Shared0Vec.Insts.Tls_codecSerializeBytes.tls_serialize_bytes inst v
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  rw [Shared0Vec.ser_eq_slice]
  exact Shared0Slice.serialize_pf inst hlaw _

/-- The `Vec<T>` serializer does not fail. -/
theorem alloc.vec.Vec.serialize_pf {T : Type} (inst : SerializeBytes T)
    (hlaw : SerializeBytes.Lawful T inst) (v : alloc.vec.Vec T) :
    ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.Insts.Tls_codecSerializeBytes.tls_serialize_bytes inst v
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  rw [alloc.vec.Vec.ser_eq_slice]
  exact Shared0Slice.serialize_pf inst hlaw _

/-- The slice serializer meets the trait-level post (partial). -/
theorem Shared0Slice.trait_fc {T : Type} (inst : SerializeBytes T)
    (hlaw : SerializeBytes.Lawful T inst) (s : Slice T) :
    ⦃ ⌜ True ⌝ ⦄ Shared0Slice.Insts.Tls_codecSerializeBytes.tls_serialize_bytes inst s
    ⦃ ⇓? res => ⌜ (SerializeBytes.tls_serialize_bytes.post
        (Shared0Slice.Insts.Tls_codecSerializeBytes inst).SizeInst
        (Shared0Slice.Insts.Tls_codecSerializeBytes inst) s res).holds ⌝ ⦄ := by
  refine partial_triple_post_mono (Shared0Slice.serialize_partial inst hlaw s) ?_
  intro r h
  cases r with
  | Ok out =>
    obtain ⟨n, hn, hl⟩ := h out rfl
    exact SerializeBytes.post_ok _ _ _ out n hn hl
  | Err e => exact SerializeBytes.post_err _ _ _ e

/-- The `&Vec<T>` serializer meets the trait-level post (partial). -/
theorem Shared0Vec.trait_fc {T : Type} (inst : SerializeBytes T)
    (hlaw : SerializeBytes.Lawful T inst) (v : alloc.vec.Vec T) :
    ⦃ ⌜ True ⌝ ⦄ Shared0Vec.Insts.Tls_codecSerializeBytes.tls_serialize_bytes inst v
    ⦃ ⇓? res => ⌜ (SerializeBytes.tls_serialize_bytes.post
        (Shared0Vec.Insts.Tls_codecSerializeBytes inst).SizeInst
        (Shared0Vec.Insts.Tls_codecSerializeBytes inst) v res).holds ⌝ ⦄ := by
  rw [Shared0Vec.ser_eq_slice]
  refine partial_triple_post_mono (Shared0Slice.serialize_partial inst hlaw _) ?_
  intro r h
  cases r with
  | Ok out =>
    obtain ⟨n, hn, hl⟩ := h out rfl
    refine SerializeBytes.post_ok _ _ _ out n ?_ hl
    show Shared0Vec.Insts.Tls_codecSize.tls_serialized_len _ v = ok n
    rw [Shared0Vec.size_eq_slice]
    exact hn
  | Err e => exact SerializeBytes.post_err _ _ _ e

/-- The `Vec<T>` serializer meets the trait-level post (partial). -/
theorem alloc.vec.Vec.ser_trait_fc {T : Type} (inst : SerializeBytes T)
    (hlaw : SerializeBytes.Lawful T inst) (v : alloc.vec.Vec T) :
    ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.Insts.Tls_codecSerializeBytes.tls_serialize_bytes inst v
    ⦃ ⇓? res => ⌜ (SerializeBytes.tls_serialize_bytes.post
        (alloc.vec.Vec.Insts.Tls_codecSerializeBytes inst).SizeInst
        (alloc.vec.Vec.Insts.Tls_codecSerializeBytes inst) v res).holds ⌝ ⦄ := by
  rw [alloc.vec.Vec.ser_eq_slice]
  refine partial_triple_post_mono (Shared0Slice.serialize_partial inst hlaw _) ?_
  intro r h
  cases r with
  | Ok out =>
    obtain ⟨n, hn, hl⟩ := h out rfl
    refine SerializeBytes.post_ok _ _ _ out n ?_ hl
    show alloc.vec.Vec.Insts.Tls_codecSize.tls_serialized_len _ v = ok n
    rw [alloc.vec.Vec.size_eq_slice]
    exact hn
  | Err e => exact SerializeBytes.post_err _ _ _ e

/-! ### Content of `TlsVarInt::write_bytes` -/

/-- One iteration of the `write_bytes` loops, on contents: byte `i-1` is OR-ed with the low byte
of `value`, which is shifted by 8. -/
theorem varint.TlsVarInt.write_bytes_loop0.body_content (bytes : Slice Std.U8) (value : Std.U64)
    (i : Std.Usize) (h : i.val ≤ bytes.val.length) :
    ⦃ ⌜ True ⌝ ⦄ varint.TlsVarInt.write_bytes_loop0.body bytes value i
    ⦃ ⇓ r => ⌜ match r with
      | .done y => i.val = 0 ∧ y = bytes
      | .cont (b', v', i') => 0 < i.val ∧ i'.val = i.val - 1 ∧ v'.val = value.val / 256 ∧
          b'.val.length = bytes.val.length ∧ ∀ k, (b'.val[k]?).map (·.val) = (bytes.val[k]?).map
            (fun x => if k = i.val - 1 then x.val ||| (value.val % 256) else x.val) ⌝ ⦄ := by
  unfold varint.TlsVarInt.write_bytes_loop0.body
  mvcgen
  · rename_i i1 hi1 hge i2 hi2 i3 hi3 i4 hi4 i5 hi5 s hlt hs v hv1 hv2 hlt8
    obtain ⟨hx, hi4v⟩ := hi4
    have h3 : i3.val = value.val % 256 := by
      subst hi3
      have h255 : value.val &&& 255 = value.val % 256 := Nat.and_two_pow_sub_one_eq_mod value.val 8
      have : i2.val = value.val &&& 255 := by simpa using hi2.1
      simp [UScalar.cast_val_eq, this, h255]
    have h5 : i5.val = i4.val ||| value.val % 256 := by rw [hi5.1]; simp [← h3]
    refine ⟨by scalar_tac, by scalar_tac, ?_, ?_, ?_⟩
    · rw [hv1]; simp [Nat.shiftRight_eq_div_pow]
    · rw [hs]; simp [Slice.set, Slice.setAtNat]
    · intro k
      subst hs
      have hk : (i1.val : ℕ) = i.val - 1 := by scalar_tac
      have h5' : i5.val = (bytes.val[i1.val]'hx).val ||| value.val % 256 := by rw [h5, hi4v]
      by_cases hkk : k = i1.val
      · subst hkk
        simp [Slice.set, Slice.setAtNat, List.getElem?_set, hx, h5']
        rw [← hk]; simp [hx]
      · simp [Slice.set, Slice.setAtNat, List.getElem?_set, hkk, Ne.symm hkk, hk ▸ hkk]
  · exfalso; scalar_tac
  · exfalso; scalar_tac
  · exfalso; scalar_tac
  · scalar_tac

/-- The `write_bytes` loops, on contents: bytes `0..i` get OR-ed with the bytes of `value`
(big-endian, the last one at index `i-1`). -/
theorem varint.TlsVarInt.write_bytes_loop0_content (bytes : Slice Std.U8) (value : Std.U64)
    (i : Std.Usize) (h : i.val ≤ bytes.val.length) :
    ⦃ ⌜ True ⌝ ⦄ varint.TlsVarInt.write_bytes_loop0 bytes value i
    ⦃ ⇓ r => ⌜ r.val.length = bytes.val.length ∧ ∀ k, (r.val[k]?).map (·.val) =
        (bytes.val[k]?).map (fun x => if k < i.val
          then x.val ||| ((value.val >>> (8 * (i.val - 1 - k))) % 256) else x.val) ⌝ ⦄ := by
  unfold varint.TlsVarInt.write_bytes_loop0
  apply Aeneas.Std.WP.spec_to_mvcgen
  apply Aeneas.Std.loop.spec_decr_nat
    (fun x : Slice Std.U8 × Std.U64 × Std.Usize => x.2.2.val)
    (fun x : Slice Std.U8 × Std.U64 × Std.Usize =>
      x.2.2.val ≤ i.val ∧ x.1.val.length = bytes.val.length ∧
      x.2.1.val = value.val >>> (8 * (i.val - x.2.2.val)) ∧
      ∀ k, (x.1.val[k]?).map (·.val) = (bytes.val[k]?).map (fun y => if x.2.2.val ≤ k ∧ k < i.val
          then y.val ||| ((value.val >>> (8 * (i.val - 1 - k))) % 256) else y.val))
    (fun y : Slice Std.U8 => y.val.length = bytes.val.length ∧ ∀ k, (y.val[k]?).map (·.val) =
        (bytes.val[k]?).map (fun x => if k < i.val
          then x.val ||| ((value.val >>> (8 * (i.val - 1 - k))) % 256) else x.val))
  · rintro ⟨b, v, j⟩ ⟨hji, hb, hv, hk⟩
    dsimp only at hji hb hv hk
    obtain ⟨r, hr, hP⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp
      (varint.TlsVarInt.write_bytes_loop0.body_content b v j (by omega))
    dsimp only
    rw [hr, Aeneas.Std.WP.spec_ok]
    cases r with
    | done y =>
      obtain ⟨hj0, rfl⟩ := hP
      refine ⟨hb, fun k => ?_⟩
      rw [hk k]
      have : (j.val ≤ k ∧ k < i.val) ↔ k < i.val := by omega
      simp only [this]
    | cont x =>
      obtain ⟨b', v', j'⟩ := x
      obtain ⟨hj, hj', hv', hl', hk'⟩ := hP
      dsimp only at hj hj' hv' hl' hk' ⊢
      refine ⟨⟨by omega, hl'.trans hb, ?_, fun k => ?_⟩, by omega⟩
      · rw [hv', hv, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
          show 8 * (i.val - j'.val) = 8 * (i.val - j.val) + 8 by omega, Nat.pow_add]
      · have hk1 := hk k
        rw [hk' k]
        rcases hy : bytes.val[k]? with _ | y
        · simp [hy] at hk1 ⊢
          simp [hk1]
        · rcases hx : b.val[k]? with _ | x
          · simp [hx, hy] at hk1
          · simp [hx, hy] at hk1 ⊢
            by_cases hkj : k = j.val - 1
            · have h1 : ¬ (j.val ≤ k ∧ k < i.val) := by omega
              have h2 : j'.val ≤ k ∧ k < i.val := by omega
              simp only [h1, if_false] at hk1
              simp only [h2, hkj, if_true, hk1, and_self]
              have h3 : j'.val ≤ j.val - 1 ∧ j.val - 1 < i.val := by omega
              rw [if_pos h3, hv, show i.val - 1 - (j.val - 1) = i.val - j.val by omega]
            · have h1 : (j.val ≤ k ∧ k < i.val) ↔ (j'.val ≤ k ∧ k < i.val) := by omega
              simp [hkj, hk1, h1]
  · refine ⟨le_refl _, rfl, by simp, fun k => ?_⟩
    have : ¬ (i.val ≤ k ∧ k < i.val) := by omega
    simp [this]

theorem varint.TlsVarInt.write_bytes_loop1_content (bytes : Slice Std.U8) (value : Std.U64)
    (i : Std.Usize) (h : i.val ≤ bytes.val.length) :
    ⦃ ⌜ True ⌝ ⦄ varint.TlsVarInt.write_bytes_loop1 bytes value i
    ⦃ ⇓ r => ⌜ r.val.length = bytes.val.length ∧ ∀ k, (r.val[k]?).map (·.val) =
        (bytes.val[k]?).map (fun x => if k < i.val
          then x.val ||| ((value.val >>> (8 * (i.val - 1 - k))) % 256) else x.val) ⌝ ⦄ := by
  have := varint.TlsVarInt.write_bytes_loop0_content bytes value i h
  unfold varint.TlsVarInt.write_bytes_loop1 varint.TlsVarInt.write_bytes_loop1.body
  unfold varint.TlsVarInt.write_bytes_loop0 varint.TlsVarInt.write_bytes_loop0.body at this
  exact this

theorem varint.TlsVarInt.write_bytes_loop2_content (bytes : Slice Std.U8) (value : Std.U64)
    (i : Std.Usize) (h : i.val ≤ bytes.val.length) :
    ⦃ ⌜ True ⌝ ⦄ varint.TlsVarInt.write_bytes_loop2 bytes value i
    ⦃ ⇓ r => ⌜ r.val.length = bytes.val.length ∧ ∀ k, (r.val[k]?).map (·.val) =
        (bytes.val[k]?).map (fun x => if k < i.val
          then x.val ||| ((value.val >>> (8 * (i.val - 1 - k))) % 256) else x.val) ⌝ ⦄ := by
  have := varint.TlsVarInt.write_bytes_loop0_content bytes value i h
  unfold varint.TlsVarInt.write_bytes_loop2 varint.TlsVarInt.write_bytes_loop2.body
  unfold varint.TlsVarInt.write_bytes_loop0 varint.TlsVarInt.write_bytes_loop0.body at this
  exact this

theorem varint.TlsVarInt.write_bytes_loop3_content (bytes : Slice Std.U8) (value : Std.U64)
    (i : Std.Usize) (h : i.val ≤ bytes.val.length) :
    ⦃ ⌜ True ⌝ ⦄ varint.TlsVarInt.write_bytes_loop3 bytes value i
    ⦃ ⇓ r => ⌜ r.val.length = bytes.val.length ∧ ∀ k, (r.val[k]?).map (·.val) =
        (bytes.val[k]?).map (fun x => if k < i.val
          then x.val ||| ((value.val >>> (8 * (i.val - 1 - k))) % 256) else x.val) ⌝ ⦄ := by
  have := varint.TlsVarInt.write_bytes_loop0_content bytes value i h
  unfold varint.TlsVarInt.write_bytes_loop3 varint.TlsVarInt.write_bytes_loop3.body
  unfold varint.TlsVarInt.write_bytes_loop0 varint.TlsVarInt.write_bytes_loop0.body at this
  exact this

/-- List-level assembly of `write_bytes`: write the prefix byte `u` at index 0 of the first `L`
bytes, OR the value bytes in (`rr`), and write the result back at index 0. -/
theorem varint.write_bytes_assemble (buf rr : List Std.U8) (L value : Nat) (u : Std.U8)
    (hL : 1 ≤ L ∧ L ≤ buf.length) (hrr : rr.length = L ∧ ∀ k, (rr[k]?).map (·.val) =
      (((buf.take L).set 0 u)[k]?).map (fun x => if k < L
        then x.val ||| ((value >>> (8 * (L - 1 - k))) % 256) else x.val)) :
    (buf.setSlice! 0 rr).length = buf.length ∧ ∀ k, ((buf.setSlice! 0 rr)[k]?).map (·.val) =
      (buf[k]?).map (fun x => if k < L then
        (if k = 0 then u.val else x.val) ||| ((value >>> (8 * (L - 1 - k))) % 256) else x.val) := by
  obtain ⟨hlen, hk⟩ := hrr
  refine ⟨by simp, fun k => ?_⟩
  by_cases hkL : k < L
  · rw [List.setSlice!_getElem?_middle _ _ _ _ ⟨by omega, by omega, by omega⟩]
    have := hk k
    simp only [Nat.sub_zero]
    rw [this]
    simp [List.getElem?_set, List.getElem?_take, hkL, show k < buf.length by omega]
    by_cases h0 : k = 0
    · subst h0; simp
    · simp [h0, Ne.symm h0]
  · rw [List.setSlice!_getElem?_suffix _ _ _ _ (by omega)]
    simp [hkL]

/-- `vec![x; len]` for `u8`, content: `len` copies of `x`. -/
theorem alloc.vec.from_elem_U8_content (item : Std.U8) (len : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ alloc.vec.from_elem core.U8.Insts.CoreCloneClone item len
    ⦃ ⇓ r => ⌜ (r : Slice Std.U8).val = List.replicate len.val item ⌝ ⦄ := by
  unfold alloc.vec.from_elem rust_primitives.sequence.seq_create
  mvcgen
  · rename_i h
    simp [Slice.new, h]
  · rename_i hne cl hcl comb hle
    rw [mapM_clone_replicate_U8] at hcl
    cases hcl
    have : (List.replicate (len.val - 1) item) ++ [item] = List.replicate len.val item := by
      rw [← List.replicate_succ']; congr 1; omega
    simpa [comb] using this
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

/-- One successful branch of `write_bytes` on contents (`len` is the encoded length, `n` the literal
the branch matched on, `u` the prefix byte). -/
theorem varint.write_bytes_case (self : varint.TlsVarInt) (buf : Slice Std.U8) (len n : Std.Usize)
    (hL : len.val = varint.lenOf self.val) (hn : n.val = len.val)
    (hle : len.val ≤ buf.val.length) (hlc : len.val = 1 ∨ len.val = 2 ∨ len.val = 4 ∨ len.val = 8)
    (p : Slice Std.U8 × (Slice Std.U8 → Slice Std.U8))
    (hp : p.1.val = buf.val.take len.val ∧ ∀ x, (p.2 x).val = buf.val.setSlice! 0 x.val)
    (u : Std.U8) (hu : u.val = varint.pfx len.val) (s s2 : Slice Std.U8)
    (hs : s = p.1.set 0#usize u)
    (hl2 : s2.val.length = s.val.length ∧ ∀ k, (s2.val[k]?).map (·.val) =
      (s.val[k]?).map (fun x => if k < n.val
        then x.val ||| ((self.val >>> (8 * (n.val - 1 - k))) % 256) else x.val)) :
    (p.2 s2).val.length = buf.val.length ∧ ∀ k, ((p.2 s2).val[k]?).map (·.val) =
      (buf.val[k]?).map (fun x => if k < varint.lenOf self.val then
        (if k = 0 then varint.pfx (varint.lenOf self.val) else x.val) |||
          ((self.val >>> (8 * (varint.lenOf self.val - 1 - k))) % 256) else x.val) := by
  rw [hp.2 s2]
  rw [hn] at hl2
  have hs' : s.val = (buf.val.take len.val).set 0 u := by
    rw [hs, ← hp.1]; simp [Slice.set, Slice.setAtNat]
  have hlen1 : 1 ≤ len.val := by omega
  have := varint.write_bytes_assemble buf.val s2.val len.val self.val u ⟨hlen1, hle⟩
    ⟨by rw [hl2.1, hs']; simp; omega, fun k => by rw [hl2.2 k, hs']⟩
  rw [← hL] at *
  rw [hu] at this
  exact this

/-- Content of `TlsVarInt::write_bytes` on a buffer of at least the encoded length: the first
`L = lenOf value` bytes are the big-endian bytes of `value`, OR-ed into the (existing) buffer, with
the length prefix `pfx L` in place of the old first byte; the rest is untouched. -/
theorem varint.TlsVarInt.write_bytes_content (self : varint.TlsVarInt) (buf : Slice Std.U8)
    (h : varint.lenOf self.val ≤ buf.val.length) :
    ⦃ ⌜ True ⌝ ⦄ varint.TlsVarInt.write_bytes self buf
    ⦃ ⇓ r => ⌜ (∃ l : Std.Usize, r.1 = .Ok l ∧ l.val = varint.lenOf self.val) ∧
        r.2.val.length = buf.val.length ∧ ∀ k, (r.2.val[k]?).map (·.val) =
        (buf.val[k]?).map (fun x => if k < varint.lenOf self.val then
          (if k = 0 then varint.pfx (varint.lenOf self.val) else x.val) |||
            ((self.val >>> (8 * (varint.lenOf self.val - 1 - k))) % 256) else x.val) ⌝ ⦄ := by
  mvcgen [varint.TlsVarInt.write_bytes, varint.TlsVarInt.write_bytes_loop0_content,
    varint.TlsVarInt.write_bytes_loop1_content, varint.TlsVarInt.write_bytes_loop2_content,
    varint.TlsVarInt.write_bytes_loop3_content]
  · rename_i len hlc blen hlt hbl
    have hc := varint.lenOf_char _ _ hlc
    exfalso; scalar_tac
  · rename_i len hlc blen hnlt hbl
    scalar_tac
  -- len = 1
  · rename_i len hlc blen hnlt hbl p hx hp s hlt hs
    have hc := varint.lenOf_char _ _ hlc
    have h2 : p.1.val.length = len.val := by rw [hp.1]; apply slice_take_length; scalar_tac
    have h3 : s.length = p.1.length := by rw [hs]; simp [Slice.set, Slice.setAtNat, Slice.length]
    scalar_tac
  · rename_i len hlc blen hnlt hbl p hx hp s hlt hs s2 buf1 hl2
    have hc := varint.lenOf_char _ _ hlc
    have hle : len.val ≤ buf.val.length := by scalar_tac
    refine ⟨⟨_, rfl, ?_⟩, ?_⟩
    · scalar_tac
    · exact varint.write_bytes_case self buf len _ hc.1 (by simp; omega) hle hc.2 p hp 0#u8
        (by simp [varint.pfx, hx]) s s2 hs hl2
  · rename_i len hlc blen hnlt hbl p hx hp ha
    have hc := varint.lenOf_char _ _ hlc
    have h2 : p.1.val.length = len.val := by rw [hp.1]; apply slice_take_length; scalar_tac
    exfalso; scalar_tac
  -- len = 2
  · rename_i len hlc blen hnlt hbl p hx hp s hlt hs
    have hc := varint.lenOf_char _ _ hlc
    have h2 : p.1.val.length = len.val := by rw [hp.1]; apply slice_take_length; scalar_tac
    have h3 : s.length = p.1.length := by rw [hs]; simp [Slice.set, Slice.setAtNat, Slice.length]
    scalar_tac
  · rename_i len hlc blen hnlt hbl p hx hp s hlt hs s2 buf1 hl2
    have hc := varint.lenOf_char _ _ hlc
    have hle : len.val ≤ buf.val.length := by scalar_tac
    refine ⟨⟨_, rfl, ?_⟩, ?_⟩
    · scalar_tac
    · exact varint.write_bytes_case self buf len _ hc.1 (by simp; omega) hle hc.2 p hp 64#u8
        (by simp [varint.pfx, hx]) s s2 hs hl2
  · rename_i len hlc blen hnlt hbl p hx hp ha
    have hc := varint.lenOf_char _ _ hlc
    have h2 : p.1.val.length = len.val := by rw [hp.1]; apply slice_take_length; scalar_tac
    exfalso; scalar_tac
  -- len = 4
  · rename_i len hlc blen hnlt hbl p hx hp s hlt hs
    have hc := varint.lenOf_char _ _ hlc
    have h2 : p.1.val.length = len.val := by rw [hp.1]; apply slice_take_length; scalar_tac
    have h3 : s.length = p.1.length := by rw [hs]; simp [Slice.set, Slice.setAtNat, Slice.length]
    scalar_tac
  · rename_i len hlc blen hnlt hbl p hx hp s hlt hs s2 buf1 hl2
    have hc := varint.lenOf_char _ _ hlc
    have hle : len.val ≤ buf.val.length := by scalar_tac
    refine ⟨⟨_, rfl, ?_⟩, ?_⟩
    · scalar_tac
    · exact varint.write_bytes_case self buf len _ hc.1 (by simp; omega) hle hc.2 p hp 128#u8
        (by simp [varint.pfx, hx]) s s2 hs hl2
  · rename_i len hlc blen hnlt hbl p hx hp ha
    have hc := varint.lenOf_char _ _ hlc
    have h2 : p.1.val.length = len.val := by rw [hp.1]; apply slice_take_length; scalar_tac
    exfalso; scalar_tac
  -- len = 8
  · rename_i len hlc blen hnlt hbl p hx hp s hlt hs
    have hc := varint.lenOf_char _ _ hlc
    have h2 : p.1.val.length = len.val := by rw [hp.1]; apply slice_take_length; scalar_tac
    have h3 : s.length = p.1.length := by rw [hs]; simp [Slice.set, Slice.setAtNat, Slice.length]
    scalar_tac
  · rename_i len hlc blen hnlt hbl p hx hp s hlt hs s2 buf1 hl2
    have hc := varint.lenOf_char _ _ hlc
    have hle : len.val ≤ buf.val.length := by scalar_tac
    refine ⟨⟨_, rfl, ?_⟩, ?_⟩
    · scalar_tac
    · exact varint.write_bytes_case self buf len _ hc.1 (by simp; omega) hle hc.2 p hp 192#u8
        (by simp [varint.pfx, hx]) s s2 hs hl2
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

/-! ### Arithmetic of the varint encoding (big-endian digits) -/

/-- Big-endian bytes of `v` on `n` digits. -/
def varint.digits (n v : Nat) : List Nat :=
  (List.range n).map (fun k => (v >>> (8 * (n - 1 - k))) % 256)

theorem varint.digits_succ (n v : Nat) :
    varint.digits (n + 1) v = ((v >>> (8 * n)) % 256) :: varint.digits n v := by
  unfold varint.digits
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  simp only [Function.comp]
  congr 3
  omega

theorem varint.foldl_digits (n v a : Nat) :
    (varint.digits n v).foldl (fun a b => a * 256 + b) a = a * 256 ^ n + v % 256 ^ n := by
  induction n generalizing a with
  | zero => simp [varint.digits, Nat.mod_one]
  | succ n ih =>
    rw [varint.digits_succ, List.foldl_cons, ih, Nat.shiftRight_eq_div_pow, pow_succ, Nat.mod_mul]
    have h2 : 2 ^ (8 * n) = 256 ^ n := by rw [pow_mul]; norm_num
    rw [h2]
    ring

/-- Big-endian value of a list of digits. -/
def varint.D (xs : List Nat) : Nat := xs.foldl (fun a b => a * 256 + b) 0

theorem varint.foldl_eq (xs : List Nat) (a : Nat) :
    xs.foldl (fun a b => a * 256 + b) a = a * 256 ^ xs.length + varint.D xs := by
  induction xs generalizing a with
  | nil => simp [varint.D]
  | cons x xs ih =>
    have hD : varint.D (x :: xs) = xs.foldl (fun a b => a * 256 + b) (0 * 256 + x) := rfl
    rw [List.foldl_cons, ih, hD, ih]
    simp only [List.length_cons, pow_succ]
    ring

theorem varint.D_cons (x : Nat) (xs : List Nat) :
    varint.D (x :: xs) = x * 256 ^ xs.length + varint.D xs := by
  have hD : varint.D (x :: xs) = xs.foldl (fun a b => a * 256 + b) (0 * 256 + x) := rfl
  rw [hD, varint.foldl_eq]; simp

theorem varint.D_lt (xs : List Nat) (h : ∀ x ∈ xs, x < 256) : varint.D xs < 256 ^ xs.length := by
  induction xs with
  | nil => simp [varint.D]
  | cons x xs ih =>
    rw [varint.D_cons, List.length_cons, pow_succ]
    have hx := h x (by simp)
    have := ih (fun y hy => h y (by simp [hy]))
    have h1 : (x + 1) * 256 ^ xs.length ≤ 256 * 256 ^ xs.length := Nat.mul_le_mul_right _ hx
    nlinarith

theorem varint.D_inj (xs ys : List Nat) (hl : xs.length = ys.length) (hx : ∀ x ∈ xs, x < 256)
    (hy : ∀ y ∈ ys, y < 256) (h : varint.D xs = varint.D ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons y ys => simp at hl
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have hl' : xs.length = ys.length := by simpa using hl
      rw [varint.D_cons, varint.D_cons, hl'] at h
      have h1 := varint.D_lt xs (fun z hz => hx z (by simp [hz]))
      have h2 := varint.D_lt ys (fun z hz => hy z (by simp [hz]))
      rw [hl'] at h1
      have hxy : x = y := by
        rcases lt_trichotomy x y with hlt | heq | hgt
        · have : (x + 1) * 256 ^ ys.length ≤ y * 256 ^ ys.length := Nat.mul_le_mul_right _ hlt
          nlinarith
        · exact heq
        · have : (y + 1) * 256 ^ ys.length ≤ x * 256 ^ ys.length := Nat.mul_le_mul_right _ hgt
          nlinarith
      subst hxy
      have : varint.D xs = varint.D ys := by omega
      rw [ih ys hl' (fun z hz => hx z (by simp [hz])) (fun z hz => hy z (by simp [hz])) this]

/-- Byte `k` of the varint encoding of `v`: the big-endian byte of `v`, with the length prefix
OR-ed into the first one. -/
def varint.encByte (v k : Nat) : Nat :=
  (if k = 0 then varint.pfx (varint.lenOf v) else 0) ||| ((v >>> (8 * (varint.lenOf v - 1 - k))) % 256)

/-- The bytes of the varint encoding of `v`. -/
def varint.encList (v : Nat) : List Nat := (List.range (varint.lenOf v)).map (varint.encByte v)

theorem varint.lenOf_mem (v : Nat) :
    varint.lenOf v = 1 ∨ varint.lenOf v = 2 ∨ varint.lenOf v = 4 ∨ varint.lenOf v = 8 := by
  unfold varint.lenOf; split_ifs <;> simp

theorem varint.lenOf_pos (v : Nat) : 1 ≤ varint.lenOf v := by
  rcases varint.lenOf_mem v with h | h | h | h <;> omega

theorem varint.encList_eq (v : Nat) :
    varint.encList v = (varint.pfx (varint.lenOf v) ||| ((v >>> (8 * (varint.lenOf v - 1))) % 256)) ::
      varint.digits (varint.lenOf v - 1) v := by
  have hpos := varint.lenOf_pos v
  obtain ⟨n, hn⟩ : ∃ n, varint.lenOf v = n + 1 := ⟨varint.lenOf v - 1, by omega⟩
  unfold varint.encList
  rw [hn, List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.add_sub_cancel]
  rw [varint.digits]
  congr 1
  · simp [varint.encByte, hn]
  · apply List.map_congr_left
    intro k _
    simp [varint.encByte, hn]
    rw [show n - (k + 1) = n - 1 - k by omega]

theorem varint.top_lt (v : Nat) (h : v ≤ 2 ^ 62 - 1) : v >>> (8 * (varint.lenOf v - 1)) < 64 := by
  rw [Nat.shiftRight_eq_div_pow]
  unfold varint.lenOf
  split_ifs <;> simp <;> omega

theorem varint.or_small (L t : Nat) (hL : L = 1 ∨ L = 2 ∨ L = 4 ∨ L = 8) (ht : t < 64) :
    varint.pfx L ||| t = varint.pfx L + t := by
  have h0 : ∀ t < 64, 0 ||| t = 0 + t := by decide
  have h1 : ∀ t < 64, 64 ||| t = 64 + t := by decide
  have h2 : ∀ t < 64, 128 ||| t = 128 + t := by decide
  have h3 : ∀ t < 64, 192 ||| t = 192 + t := by decide
  rcases hL with rfl | rfl | rfl | rfl
  · simpa [varint.pfx] using h0 t ht
  · simpa [varint.pfx] using h1 t ht
  · simpa [varint.pfx] using h2 t ht
  · simpa [varint.pfx] using h3 t ht

theorem varint.pfx_inj (L L' : Nat) (hL : L = 1 ∨ L = 2 ∨ L = 4 ∨ L = 8)
    (hL' : L' = 1 ∨ L' = 2 ∨ L' = 4 ∨ L' = 8) (h : varint.pfx L = varint.pfx L') : L = L' := by
  rcases hL with rfl | rfl | rfl | rfl <;> rcases hL' with rfl | rfl | rfl | rfl <;>
    simp_all [varint.pfx]

theorem varint.pfx_mem (L : Nat) (hL : L = 1 ∨ L = 2 ∨ L = 4 ∨ L = 8) :
    varint.pfx L = 0 ∨ varint.pfx L = 64 ∨ varint.pfx L = 128 ∨ varint.pfx L = 192 := by
  rcases hL with rfl | rfl | rfl | rfl <;> simp [varint.pfx]

/-- Decoding the encoding: the first byte has the length prefix, and folding its low 6 bits with
the other bytes gives back the value. -/
theorem varint.encList_dec (v : Nat) (h : v ≤ 2 ^ 62 - 1) :
    ∃ e0 tl, varint.encList v = e0 :: tl ∧ e0 / 64 * 64 = varint.pfx (varint.lenOf v) ∧
      tl.length = varint.lenOf v - 1 ∧ (∀ x ∈ e0 :: tl, x < 256) ∧
      varint.D ((e0 % 64) :: tl) = v := by
  have hL := varint.lenOf_mem v
  have htop := varint.top_lt v h
  set L := varint.lenOf v with hLdef
  have hm : (v >>> (8 * (L - 1))) % 256 = v >>> (8 * (L - 1)) := Nat.mod_eq_of_lt (by omega)
  have hor := varint.or_small L _ hL htop
  have hp := varint.pfx_mem L hL
  refine ⟨_, _, varint.encList_eq v, ?_, ?_, ?_, ?_⟩
  · rw [hm, hor]; omega
  · show (varint.digits (L - 1) v).length = L - 1
    simp [varint.digits]
  · intro x hx
    rw [hm, hor] at hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · simp only [varint.digits, List.mem_map] at hx
      obtain ⟨k, _, rfl⟩ := hx
      exact Nat.mod_lt _ (by norm_num)
  · rw [hm, hor]
    have e : (varint.pfx L + v >>> (8 * (L - 1))) % 64 = v >>> (8 * (L - 1)) := by omega
    rw [e, varint.D, List.foldl_cons, varint.foldl_digits]
    have hlt : v < 2 ^ (8 * (L - 1)) * 64 := by
      rw [Nat.shiftRight_eq_div_pow] at htop
      have := Nat.div_lt_iff_lt_mul (Nat.two_pow_pos (8 * (L - 1))) |>.mp htop
      rw [Nat.mul_comm]; exact this
    have h256 : (256 : Nat) ^ (L - 1) = 2 ^ (8 * (L - 1)) := by rw [pow_mul]; norm_num
    rw [Nat.shiftRight_eq_div_pow, ← h256, Nat.zero_mul, Nat.zero_add, Nat.mul_comm]
    exact Nat.div_add_mod v _

/-- Canonical encoding (decode then encode): what the decoder reads is the encoding of the value. -/
theorem varint.enc_of_dec (b0 : Nat) (l : List Nat) (L v : Nat) (hv : v ≤ 2 ^ 62 - 1)
    (hb0 : b0 < 256) (hl : ∀ x ∈ l, x < 256) (hL : L = varint.lenOf v)
    (hpfx : varint.pfx L = b0 / 64 * 64) (hle : L - 1 ≤ l.length)
    (hval : v = (l.take (L - 1)).foldl (fun a b => a * 256 + b) (b0 % 64)) :
    b0 :: l.take (L - 1) = varint.encList v := by
  obtain ⟨e0, tl, he, he0, htl, hlt, hD⟩ := varint.encList_dec v hv
  rw [he]
  have hlen : (b0 % 64 :: l.take (L - 1)).length = (e0 % 64 :: tl).length := by
    simp [htl, hL]; omega
  have hDeq : varint.D (b0 % 64 :: l.take (L - 1)) = varint.D (e0 % 64 :: tl) := by
    rw [hD, varint.D_cons, hval, varint.foldl_eq]
  have hall1 : ∀ x ∈ b0 % 64 :: l.take (L - 1), x < 256 := by
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · exact hl x (List.mem_of_mem_take hx)
  have hall2 : ∀ x ∈ e0 % 64 :: tl, x < 256 := by
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · exact hlt x (by simp [hx])
  have := varint.D_inj _ _ hlen hall1 hall2 hDeq
  simp only [List.cons.injEq] at this
  rw [← hL] at he0
  have hb : b0 = e0 := by omega
  rw [hb, this.2]

/-- Round trip (encode then decode): decoding the encoding of `v` returns `v`, consuming it all. -/
theorem varint.dec_of_enc (b0 : Nat) (l : List Nat) (L v v' : Nat) (hv : v ≤ 2 ^ 62 - 1)
    (hc : b0 :: l = varint.encList v) (hL : L = 1 ∨ L = 2 ∨ L = 4 ∨ L = 8)
    (hpfx : varint.pfx L = b0 / 64 * 64)
    (hval : v' = (l.take (L - 1)).foldl (fun a b => a * 256 + b) (b0 % 64)) :
    L = varint.lenOf v ∧ l.length = L - 1 ∧ v' = v := by
  obtain ⟨e0, tl, he, he0, htl, hlt, hD⟩ := varint.encList_dec v hv
  rw [he] at hc
  obtain ⟨rfl, rfl⟩ := List.cons.inj hc
  have hLL : L = varint.lenOf v :=
    varint.pfx_inj _ _ hL (varint.lenOf_mem v) (hpfx.trans he0)
  have hl : l.length = L - 1 := by rw [htl, hLL]
  refine ⟨hLL, hl, ?_⟩
  rw [hval, List.take_of_length_le (by omega), ← hD, varint.D_cons, varint.foldl_eq]

/-- Content of `TlsVarInt::tls_serialize_bytes`: never fails, returns the `lenOf` bytes `encByte`. -/
theorem varint.TlsVarInt.serialize_content (self : varint.TlsVarInt) :
    ⦃ ⌜ True ⌝ ⦄ varint.TlsVarInt.Insts.Tls_codecSerializeBytes.tls_serialize_bytes self
    ⦃ ⇓ r => ⌜ ∃ v : alloc.vec.Vec Std.U8, r = .Ok v ∧
        (v : Slice Std.U8).val.map (·.val) =
          (List.range (varint.lenOf self.val)).map (varint.encByte self.val) ⌝ ⦄ := by
  mvcgen [varint.TlsVarInt.Insts.Tls_codecSerializeBytes.tls_serialize_bytes,
    varint.TlsVarInt.bytes_len_spec, alloc.vec.from_elem_U8_content,
    varint.TlsVarInt.write_bytes_content, alloc.vec.Vec.Insts.CoreOpsDerefDerefMutSlice.deref_mut,
    alloc.vec.Vec.as_mut_slice, rust_primitives.sequence.seq_to_slice_mut]
  · rename_i len hlc vec hvl back
    have hc := varint.lenOf_char _ _ hlc
    rw [hvl]; simp; omega
  · rename_i len hlc vec hvl back wr hwr cf val hx byt hcf
    have hc := varint.lenOf_char _ _ hlc
    obtain ⟨_, _, hk⟩ := hwr
    refine ⟨_, rfl, ?_⟩
    show wr.2.val.map (·.val) = _
    apply List.ext_getElem?
    intro k
    have hk' := hk k
    rw [List.getElem?_map, hk', hvl, List.getElem?_replicate, List.getElem?_map]
    by_cases hkL : k < varint.lenOf self.val
    · have hkl : k < len.val := by omega
      rw [List.getElem?_range hkL]
      simp [hkL, hkl, varint.encByte]
    · have hkl : ¬ k < len.val := by omega
      rw [List.getElem?_eq_none (by simp; omega)]
      simp [hkL, hkl]
  · rename_i len hlc vec hvl back wr hwr cf resid hx
    obtain ⟨⟨l, hl, _⟩, _⟩ := hwr
    intro hb
    rw [hl] at hb
    simp only [tryCF, reduceCtorEq] at hb


/-! ### Trait contracts of `u16`

The `Lawful` structures of `u16` (the generic `Vec<T>` results take them as hypotheses). -/

theorem U16.size_lawful : Size.Lawful Std.U16 U16.Insts.Tls_codecSize :=
  ⟨fun x _ => by
    obtain ⟨v, hv, -⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp
      (show ⦃ ⌜ True ⌝ ⦄ U16.Insts.Tls_codecSize.tls_serialized_len x ⦃ ⇓ _ => ⌜ True ⌝ ⦄ by
        mvcgen [U16.Insts.Tls_codecSize.tls_serialized_len])
    show ⦃ ⌜ True ⌝ ⦄ U16.Insts.Tls_codecSize.tls_serialized_len x
      ⦃ ⇓ r => ⌜ (Size.tls_serialized_len.post U16.Insts.Tls_codecSize x r).holds ⌝ ⦄
    rw [hv]
    apply RustM.ok_spec
    unfold Size.tls_serialized_len.post
    mvcgen⟩

theorem U16.serialize_lawful : SerializeBytes.Lawful Std.U16 U16.Insts.Tls_codecSerializeBytes where
  SizeInstLawful := U16.size_lawful
  tls_serialize_bytes_spec x _ := by
    apply triple_post_mono (U16_serialize_char x)
    rintro r ⟨v, rfl, hv⟩
    refine SerializeBytes.post_ok _ _ _ v 2#usize rfl ?_
    rw [hv]; simpa using (Aeneas.Std.core.num.U16.to_be_bytes x).property

theorem U16.deserialize_post (b : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ U16.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes b
    ⦃ ⇓ r => ⌜ (DeserializeBytes.tls_deserialize_bytes.post U16.Insts.Tls_codecSize
        U16.Insts.Tls_codecDeserializeBytes b r).holds ⌝ ⦄ := by
  apply triple_post_mono (U16_deserialize_char b)
  intro r hP
  by_cases hl : 2 ≤ b.val.length
  · obtain ⟨a, t, ha, ht, rfl⟩ := hP.1 hl
    refine DeserializeBytes.post_ok _ _ _ _ _ 2#usize rfl ?_
    simp [ht]; omega
  · rw [hP.2 (by omega)]
    exact DeserializeBytes.post_err _ _ _ _

theorem U16.deserialize_lawful :
    DeserializeBytes.Lawful Std.U16 U16.Insts.Tls_codecDeserializeBytes where
  SizeInstLawful := U16.size_lawful
  tls_deserialize_bytes_spec b _ := U16.deserialize_post b
  tls_deserialize_exact_bytes_spec b _ :=
    total_of_pf_partial
      (DeserializeBytes.exact_default_pf U16.Insts.Tls_codecDeserializeBytes
        (fun b => pf_of_total (U16.deserialize_post b)) b)
      (DeserializeBytes.exact_default_fc U16.Insts.Tls_codecDeserializeBytes b
        (partial_of_total (U16.deserialize_post b)))


/-! ### Content of the length-prefixed serializers and deserializers

Encoding form: bytes are compared through `(·.val)` as naturals, the length prefix is
`varint.encList n`. -/

/-- The varint encoding is prefix-free: equal encodings followed by anything determine the value. -/
theorem varint.encList_append_inj (n v : Nat) (X Y : List Nat) (hn : n ≤ 2 ^ 62 - 1)
    (hv : v ≤ 2 ^ 62 - 1) (h : varint.encList n ++ X = varint.encList v ++ Y) : n = v ∧ X = Y := by
  obtain ⟨e0, tl, he, he0, htl, -, hD⟩ := varint.encList_dec n hn
  obtain ⟨e0', tl', he', he0', htl', -, hD'⟩ := varint.encList_dec v hv
  rw [he, he', List.cons_append, List.cons_append] at h
  obtain ⟨rfl, h2⟩ := List.cons.inj h
  have hL : varint.lenOf n = varint.lenOf v :=
    varint.pfx_inj _ _ (varint.lenOf_mem n) (varint.lenOf_mem v) (he0.symm.trans he0')
  obtain ⟨rfl, rfl⟩ := List.append_inj h2 (by rw [htl, htl', hL])
  exact ⟨hD.symm.trans hD', rfl⟩

/-- `TlsVarInt::tls_deserialize_bytes` on contents, in encoding form: on success the input is the
minimal encoding of the value followed by the remainder. -/
theorem varint.TlsVarInt.deserialize_enc (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ varint.TlsVarInt.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : varint.TlsVarInt) (t : Slice Std.U8), r = .Ok (v, t) →
        v.val ≤ 2 ^ 62 - 1 ∧
        bytes.val.map (·.val) = varint.encList v.val ++ t.val.map (·.val) ⌝ ⦄ := by
  apply triple_post_mono (varint.TlsVarInt.deserialize_content bytes)
  intro r hr v t hrt
  obtain ⟨b0, l, L, hbl, hL, hLv, hpfx, hle, ht, hval, hmax⟩ := hr v t hrt
  refine ⟨hmax, ?_⟩
  have hb0 : b0.val < 256 := by have := b0.hBounds; simpa using this
  have hl : ∀ x ∈ l.map (·.val), x < 256 := by
    simp only [List.mem_map]; rintro _ ⟨a, -, rfl⟩; have := a.hBounds; simpa using this
  have hE := varint.enc_of_dec b0.val (l.map (·.val)) L v.val hmax hb0 hl hLv hpfx
    (by simpa using hle) (by rw [hval, ← List.map_take, List.foldl_map])
  rw [← hE, hbl, ht, List.map_cons, List.cons_append, ← List.map_take, ← List.map_append,
    List.take_append_drop]

/-- One iteration of the varint loop with enough input left (`len - i` bytes): it does not fail. -/
theorem varint.deserialize_loop.body_total (len : Std.Usize) (remainder : Slice Std.U8)
    (value : Std.U64) (i : Std.Usize) (hi : 1 ≤ i.val) (hil : i.val ≤ len.val) (hl : len.val ≤ 8)
    (hv : value.val < 2 ^ (8 * i.val - 2)) (hrem : len.val - i.val ≤ remainder.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    varint.TlsVarInt.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes_loop.body len remainder value i
    ⦃ ⇓ r => ⌜ match r with
      | .done (_, _, f) => f = core.option.Option.None
      | .cont (r', v', i') => r'.val.length + 1 = remainder.val.length ∧ i'.val = i.val + 1 ∧
          i'.val ≤ len.val ∧ v'.val < 2 ^ (8 * i'.val - 2) ⌝ ⦄ := by
  unfold varint.TlsVarInt.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes_loop.body
  mvcgen [U8_deserialize_char]
  · rename_i hlt r0 p hr hP r3 h3 h3b h3c r2 h2 r1 h1 r h0
    have hb := varint.step_bound value.val r2.val i.val hi (by scalar_tac) hv (by scalar_tac)
    obtain ⟨a, t, ha, ht, hpt⟩ := hP.1 (by scalar_tac)
    rw [(congrArg Prod.snd (core.result.Result.Ok.inj hpt)).trans rfl, ht]
    simp only [List.length_drop]
    have h1' : (1#usize).val = 1 := by simp
    refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, ?_⟩
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
  · rename_i hlt r0 e hr hP
    obtain ⟨a, t, -, -, h⟩ := hP.1 (by scalar_tac)
    cases h

/-- The varint loop does not fail when `len - i` bytes are available. -/
theorem varint.deserialize_loop_total (remainder : Slice Std.U8) (len : Std.Usize)
    (value : Std.U64) (i : Std.Usize) (hi : 1 ≤ i.val) (hil : i.val ≤ len.val) (hl : len.val ≤ 8)
    (hv : value.val < 2 ^ (8 * i.val - 2)) (hrem : len.val - i.val ≤ remainder.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    varint.TlsVarInt.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes_loop remainder len value i
    ⦃ ⇓ r => ⌜ r.2.2 = core.option.Option.None ⌝ ⦄ := by
  unfold varint.TlsVarInt.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes_loop
  apply Aeneas.Std.WP.spec_to_mvcgen
  apply Aeneas.Std.loop.spec_decr_nat
    (fun x : Slice Std.U8 × Std.U64 × Std.Usize => len.val - x.2.2.val)
    (fun x : Slice Std.U8 × Std.U64 × Std.Usize =>
      1 ≤ x.2.2.val ∧ x.2.2.val ≤ len.val ∧ x.2.1.val < 2 ^ (8 * x.2.2.val - 2) ∧
      len.val - x.2.2.val ≤ x.1.val.length)
    (fun y : Slice Std.U8 × Std.U64 × (core.option.Option Error) => y.2.2 = core.option.Option.None)
  · rintro ⟨b, v, j⟩ ⟨hj1, hjl, hjv, hjr⟩
    dsimp only at hj1 hjl hjv hjr
    obtain ⟨r, hr, hP⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp
      (varint.deserialize_loop.body_total len b v j hj1 hjl hl hjv hjr)
    dsimp only
    rw [hr, Aeneas.Std.WP.spec_ok]
    cases r with
    | done y => exact hP
    | cont x =>
      obtain ⟨b', v', j'⟩ := x
      obtain ⟨h1, h2, h3, h4⟩ := hP
      dsimp only at h1 h2 h3 h4 ⊢
      exact ⟨⟨by omega, h3, h4, by omega⟩, by omega⟩
  · exact ⟨hi, hil, hv, hrem⟩

/-- The varint loop on enough input: it succeeds, and the content facts hold. -/
theorem varint.deserialize_loop_full (remainder : Slice Std.U8) (len : Std.Usize)
    (value : Std.U64) (i : Std.Usize) (hi : 1 ≤ i.val) (hil : i.val ≤ len.val) (hl : len.val ≤ 8)
    (hv : value.val < 2 ^ (8 * i.val - 2)) (hrem : len.val - i.val ≤ remainder.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    varint.TlsVarInt.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes_loop remainder len value i
    ⦃ ⇓ r => ⌜ r.2.2 = core.option.Option.None ∧
        r.1.val = remainder.val.drop (len.val - i.val) ∧
        r.2.1.val = (remainder.val.take (len.val - i.val)).foldl (fun a b => a * 256 + b.val) value.val ⌝ ⦄ :=
  triple_post_mono
    (triple_and (varint.deserialize_loop_total remainder len value i hi hil hl hv hrem)
      (varint.deserialize_loop_content remainder len value i hi hil hl hv))
    fun _ ⟨h1, h2⟩ => ⟨h1, (h2 h1).2⟩

/-- Facts shared by the verification conditions of `deserialize_ok`: the first byte `p.1` read by
`u8::tls_deserialize_bytes` heads the encoding of `n`, `calculate_value` recovers the length and the
low 6 bits, and the fold of the next bytes gives `n`. -/
theorem varint.deserialize_ok_facts {bytes : Slice Std.U8} {n : Nat} {rest : List Nat}
    {r0 : core.result.Result (Std.U8 × Slice Std.U8) Error} {p : Std.U8 × Slice Std.U8}
    {r1 : core.result.Result (Std.Usize × Std.Usize) Error} {val : Std.Usize × Std.Usize}
    {r2 : core.result.Result Std.U64 core.num.error.TryFromIntError} {t val1 : Std.U64}
    (hn : n ≤ 2 ^ 62 - 1) (hb : bytes.val.map (·.val) = varint.encList n ++ rest)
    (hP : (1 ≤ bytes.val.length → ∃ (a : Aeneas.Std.Array Std.U8 1#usize) (t : Slice Std.U8),
          a.val = bytes.val.take 1 ∧ t.val = bytes.val.drop 1 ∧
          r0 = .Ok (Aeneas.Std.core.num.U8.from_be_bytes a, t)) ∧
        (bytes.val.length < 1 → r0 = .Err Error.EndOfStream))
    (hcf : core.ops.control_flow.ControlFlow.Continue p = tryCF r0)
    (hvl : ∃ v l : Std.Usize, r1 = .Ok (v, l) ∧ v.val = p.1.val % 64 ∧
        (l.val = 1 ∨ l.val = 2 ∨ l.val = 4 ∨ l.val = 8) ∧ varint.pfx l.val = p.1.val / 64 * 64)
    (hcf1 : core.ops.control_flow.ControlFlow.Continue val = tryCF r1)
    (h2 : r2 = .Ok (UScalar.cast .U64 val.1)) (ha : r2 = .Ok t)
    (hcf2 : core.ops.control_flow.ControlFlow.Continue val1 =
      tryCF (core.result.Result.Ok t : core.result.Result Std.U64 Error)) :
    ∃ tl, varint.encList n = p.1.val :: tl ∧ p.2.val.map (·.val) = tl ++ rest ∧
      val.2.val = varint.lenOf n ∧ tl.length = varint.lenOf n - 1 ∧ val1.val = p.1.val % 64 ∧
      (p.2.val.take (val.2.val - 1)).foldl (fun a b => a * 256 + b.val) val1.val = n := by
  obtain ⟨l, hbl, hp2⟩ := U8_deserialize_ok hP hcf
  obtain ⟨e0, tl, he, he0, htl, -, hD⟩ := varint.encList_dec n hn
  rw [hbl, he, List.map_cons, List.cons_append, List.cons.injEq] at hb
  obtain ⟨hb0, hbl'⟩ := hb
  obtain ⟨v, l', hr1, hv, hl', hpf⟩ := hvl
  rw [continue_eq_tryCF, hr1, core.result.Result.Ok.injEq] at hcf1
  subst hcf1
  rw [continue_eq_tryCF, core.result.Result.Ok.injEq] at hcf2
  subst hcf2
  have hLL : l'.val = varint.lenOf n :=
    varint.pfx_inj _ _ hl' (varint.lenOf_mem n) (hpf.trans (by rw [hb0, he0]))
  have hv1 : t.val = p.1.val % 64 := by
    have := core.result.Result.Ok.inj (h2.symm.trans ha)
    rw [← this]; simpa using hv
  have hk : l'.val - 1 = tl.length := by rw [hLL, htl]
  refine ⟨tl, by rw [he, hb0], by rw [hp2]; exact hbl', hLL, htl, hv1, ?_⟩
  simp only
  rw [hk, hp2, hv1, show (l.take tl.length).foldl (fun a (b : Std.U8) => a * 256 + b.val) (p.1.val % 64) =
      ((l.map (·.val)).take tl.length).foldl (fun a b => a * 256 + b) (p.1.val % 64) by
    rw [← List.map_take, List.foldl_map], hbl', List.take_left' rfl, varint.foldl_eq, ← hD,
    varint.D_cons, hb0]

set_option hygiene false in
/-- Context of the verification conditions of `varint.TlsVarInt.deserialize_ok`: names the
hypotheses and derives `varint.deserialize_ok_facts` (hygiene is off on purpose, the names are used
by the callers). -/
macro "deser_ok_ctx" : tactic =>
  `(tactic| (rename_i r0 hP cf0 p hx hcf r1 hvl cf1 val hx1 hcf1 r2 h2 t ha cf2 val1 hx2 hcf2
             obtain ⟨tl, -, hp2, hL, htl, hv1, hfold⟩ :=
               varint.deserialize_ok_facts hn hb hP hcf hvl hcf1 h2 ha hcf2
             have hlm := varint.lenOf_mem n))

/-- `TlsVarInt::tls_deserialize_bytes` succeeds on the encoding of a value at most `MAX`
(followed by anything). -/
theorem varint.TlsVarInt.deserialize_ok (bytes : Slice Std.U8) (n : Nat) (rest : List Nat)
    (hn : n ≤ 2 ^ 62 - 1) (hb : bytes.val.map (·.val) = varint.encList n ++ rest) :
    ⦃ ⌜ True ⌝ ⦄ varint.TlsVarInt.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes bytes
    ⦃ ⇓ r => ⌜ ∃ p, r = .Ok p ⌝ ⦄ := by
  mvcgen [varint.TlsVarInt.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes,
    U8_deserialize_char, varint.calculate_value_content,
    core.result.Result.map_err_spec, varint.deserialize_loop_full,
    varint.DeserializeBytesTlsVarInt.tls_deserialize_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError.call_once]
  · deser_ok_ctx
    scalar_tac
  · deser_ok_ctx
    scalar_tac
  · deser_ok_ctx
    have h1 : (1#usize).val = 1 := by simp
    rw [h1]
    omega
  · deser_ok_ctx
    have := congrArg List.length hp2
    simp only [List.length_map, List.length_append] at this
    scalar_tac
  · rename_i r hnone hloop
    deser_ok_ctx
    have hr : r.2.1.val = n := by rw [hloop.2.2]; simpa using hfold
    have hc := varint.check_min_len_total r.2.1 val.2 (by omega) (by rw [hr]; omega)
    mvcgen [hc]
    · exact ⟨_, rfl⟩
    · rename_i r4 h4 cf3 resid hx3
      intro hbr
      exfalso
      rw [h4] at hbr
      simp only [tryCF, reduceCtorEq] at hbr
  · rename_i r0 hP cf0 p hx hcf r1 hvl cf1 val hx1 hcf1 r2 h2 t ha cf2 val1 hx2 hcf2 r e hsome hloop
    rw [hloop.1] at hsome
    cases hsome
  · rename_i r0 hP cf0 p hx hcf r1 hvl cf1 val hx1 hcf1 r2 h2 t ha cf2 resid hx2
    intro hb
    exfalso
    simp only [tryCF, reduceCtorEq] at hb
  · rename_i r0 hP cf0 p hx hcf r1 hvl cf1 val hx1 hcf1 r2 h2 e ha
    exfalso
    rw [h2] at ha
    cases ha
  · rename_i r0 hP cf0 p hx hcf r1 hvl cf1 resid hx1
    obtain ⟨v, l, hr, -⟩ := hvl
    intro hb
    exfalso
    rw [hr] at hb
    simp only [tryCF, reduceCtorEq] at hb
  · rename_i r0 hP cf0 resid hx
    intro hbr
    exfalso
    obtain ⟨e0, tl, he, -⟩ := varint.encList_dec n hn
    have hlen := congrArg List.length hb
    simp only [he, List.length_map, List.length_append, List.length_cons] at hlen
    obtain ⟨a, t, -, -, hr⟩ := hP.1 (by omega)
    rw [hr] at hbr
    simp only [tryCF, reduceCtorEq] at hbr

/-- `varint.TlsVarInt.deserialize_content` together with `deserialize_ok`: a round-trip proof needs
both the content of an `Ok` result and that the call is `Ok` on an encoding. -/
theorem varint.TlsVarInt.deserialize_content_ok (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ varint.TlsVarInt.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes bytes
    ⦃ ⇓ r => ⌜ (∀ (v : varint.TlsVarInt) (t : Slice Std.U8), r = .Ok (v, t) →
        ∃ (b0 : Std.U8) (l : List Std.U8) (L : Nat), bytes.val = b0 :: l ∧
          (L = 1 ∨ L = 2 ∨ L = 4 ∨ L = 8) ∧ L = varint.lenOf v.val ∧ varint.pfx L = b0.val / 64 * 64 ∧
          L - 1 ≤ l.length ∧ t.val = l.drop (L - 1) ∧
          v.val = (l.take (L - 1)).foldl (fun a b => a * 256 + b.val) (b0.val % 64) ∧
          v.val ≤ 2 ^ 62 - 1) ∧
        ((∃ (n : Nat) (rest : List Nat), n ≤ 2 ^ 62 - 1 ∧
            bytes.val.map (·.val) = varint.encList n ++ rest) → ∃ p, r = .Ok p) ⌝ ⦄ := by
  refine triple_and (varint.TlsVarInt.deserialize_content bytes) ?_
  by_cases h : ∃ (n : Nat) (rest : List Nat), n ≤ 2 ^ 62 - 1 ∧
      bytes.val.map (·.val) = varint.encList n ++ rest
  · obtain ⟨n, rest, hn, hb⟩ := h
    exact triple_post_mono (varint.TlsVarInt.deserialize_ok bytes n rest hn hb) fun _ h _ => h
  · exact triple_post_mono (varint.TlsVarInt.deserialize_content bytes) fun _ _ h' => absurd h' h

/-- `ContentLength::tls_deserialize_bytes` on contents, in encoding form. -/
theorem quic_vec.ContentLength.deserialize_content (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ quic_vec.ContentLength.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : quic_vec.ContentLength) (t : Slice Std.U8), r = .Ok (v, t) →
        v.val ≤ 2 ^ 30 - 1 ∧ bytes.val.map (·.val) = varint.encList v.val ++ t.val.map (·.val) ⌝ ⦄ := by
  mvcgen [quic_vec.ContentLength.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes,
    varint.TlsVarInt.deserialize_enc, quic_vec.ContentLength.new, varint.TlsVarInt.value,
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

/-- Proof of `VLBytes.deserialize_content` and `VLByteVec.deserialize_content` (the two
deserializers are the same code up to the wrapper `new`). -/
syntax "vl_deserialize_content " ident ident : tactic
macro_rules
  | `(tactic| vl_deserialize_content $fn $new) => `(tactic| (
    mvcgen [$fn:ident, quic_vec.ContentLength.deserialize_content, varint.TlsVarInt.value,
      $new:ident, core.option.Option.ok_or_spec, core.Slice.Insts.CoreOpsIndexIndex.index_spec,
      alloc.vec.Vec.new_spec, core.hint.must_use_spec]
    try_vcs
    all_goals (try simp only [continue_eq_tryCF] at *)
    · rename_i r0 hP r1 p x1 r2 htf r3 val x2 hv0 rv hrv h3 h5
      intro v t h
      obtain ⟨hv1, hv2⟩ := Prod.mk.inj (core.result.Result.Ok.inj h)
      subst hv1 hv2
      have hp := hP p.1 p.2 h3
      have hy := htf.1 val h5
      have hv : val.val = 0 := by rw [hv0]; rfl
      have hrl : rv.val = [] := by rw [hrv]; simp [Slice.new]
      refine ⟨by simp [hrl], ?_⟩
      rw [hp.2, hrl]
      simp [show p.1.val = 0 by omega]
    · rename_i r0 hP r1 p x1 r2 htf r3 val x2 hv0 o ho rr vec hrr hok rv hrv ro h3 h5
      intro hd hn
      have hb := hP p.1 p.2 h3
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
      intro v t' h
      obtain ⟨hv1, hv2⟩ := Prod.mk.inj (core.result.Result.Ok.inj h)
      subst hv1 hv2
      have hrl : rv.val = p.2.val.take val.val := by rw [hrv, ← hvec, ht']
      have hlen : rv.val.length = p.1.val := by
        rw [hrl, List.length_take]; omega
      refine ⟨by simp only; omega, ?_⟩
      simp only
      rw [hb.2, hlen, hrl, h2', List.append_assoc, ← List.map_append, ← hy,
        List.take_append_drop]
    · intro v t h; cases h
    · exfalso
      rename_i r0 hP r1 p x1 r2 htf r3 residual x2 e hr2 h3
      have hb := hP p.1 p.2 h3
      obtain ⟨y, hy⟩ := htf.2 (by omega)
      rw [hy] at hr2
      cases hr2
    · intro _ v t h; cases h))

/-- `VLBytes::tls_deserialize_bytes` on contents: the input is the length prefix, the payload and
the remainder. -/
theorem quic_vec.VLBytes.deserialize_content (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ quic_vec.VLBytes.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : quic_vec.VLBytes) (t : Slice Std.U8), r = .Ok (v, t) →
        v.vec.val.length ≤ 2 ^ 30 - 1 ∧ bytes.val.map (·.val) =
          varint.encList v.vec.val.length ++ v.vec.val.map (·.val) ++ t.val.map (·.val) ⌝ ⦄ := by
  vl_deserialize_content quic_vec.VLBytes.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes
    quic_vec.VLBytes.new

/-- `VLByteVec::tls_deserialize_bytes` on contents. -/
theorem quic_vec.VLByteVec.deserialize_content (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ quic_vec.VLByteVec.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ (v : quic_vec.VLByteVec) (t : Slice Std.U8), r = .Ok (v, t) →
        v.vec.val.length ≤ 2 ^ 30 - 1 ∧ bytes.val.map (·.val) =
          varint.encList v.vec.val.length ++ v.vec.val.map (·.val) ++ t.val.map (·.val) ⌝ ⦄ := by
  vl_deserialize_content quic_vec.VLByteVec.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes
    quic_vec.VLByteVec.new

/-- `Vec::<u8>::resize` of an empty vector: `n` copies of `x`. -/
theorem alloc.vec.Vec.resize_U8_content (v : alloc.vec.Vec Std.U8) (n : Std.Usize) (x : Std.U8)
    (hv : (v : Slice Std.U8).val = []) :
    ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.resize core.U8.Insts.CoreCloneClone v n x
    ⦃ ⇓ r => ⌜ (r : Slice Std.U8).val = List.replicate n.val x ⌝ ⦄ := by
  unfold alloc.vec.Vec.resize rust_primitives.sequence.seq_create
  simp only [mapM_clone_replicate_U8]
  mvcgen
  all_goals (simp_all +zetaDelta [Slice.new])
  all_goals (first | scalar_tac | (rw [← List.replicate_succ']; congr 1; omega))

/-- The prefix `write_bytes` writes into `lenOf n` zero bytes is the varint encoding of `n`. -/
theorem varint.write_prefix_content (n : Nat) (w : List Std.U8)
    (hk : ∀ k, (w[k]?).map (·.val) =
        ((List.replicate (varint.lenOf n) (0#u8))[k]?).map (fun x => if k < varint.lenOf n then
          (if k = 0 then varint.pfx (varint.lenOf n) else x.val) |||
            ((n >>> (8 * (varint.lenOf n - 1 - k))) % 256) else x.val)) :
    w.map (·.val) = varint.encList n := by
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_map, hk, List.getElem?_replicate]
  unfold varint.encList
  rw [List.getElem?_map]
  by_cases hkL : k < varint.lenOf n
  · rw [List.getElem?_range hkL]
    simp [hkL, varint.encByte]
  · rw [List.getElem?_eq_none (by simp; omega)]
    simp [hkL]

/-- `VLBytes::tls_serialize_bytes` on contents: an `Ok` output is the length prefix and the
payload (and the payload is within the MLS bound). -/
theorem quic_vec.VLBytes.serialize_content (self : quic_vec.VLBytes) :
    ⦃ ⌜ True ⌝ ⦄ quic_vec.VLBytes.Insts.Tls_codecSerializeBytes.tls_serialize_bytes self
    ⦃ ⇓ r => ⌜ ∀ out, r = .Ok out → self.vec.val.length ≤ 2 ^ 30 - 1 ∧
        out.val.map (·.val) = varint.encList self.vec.val.length ++ self.vec.val.map (·.val) ⌝ ⦄ := by
  mvcgen [quic_vec.VLBytes.Insts.Tls_codecSerializeBytes.tls_serialize_bytes,
    quic_vec.VLBytes.as_slice, quic_vec.VLBytes.impl.vec, alloc.vec.Vec.with_capacity,
    alloc.vec.Vec.resize_U8_content, checked_alloc_len_small,
    alloc.vec.Vec.Insts.CoreOpsDerefDerefMutSlice.deref_mut, alloc.vec.Vec.as_mut_slice,
    rust_primitives.sequence.seq_to_slice_mut, varint.TlsVarInt.write_bytes_content,
    alloc.vec.Vec.Insts.CoreIterTraitsCollectExtendSharedAT.extend_slice_spec]
  all_goals (try simp only [continue_eq_tryCF] at *)
  all_goals subst_vars
  all_goals (try simp only [Slice.len_val] at *)
  case vc1.h => rename_i hr hv; have := hr.2.1; omega
  case vc2.hv => rfl
  case vc3.h =>
    have hc := varint.lenOf_char _ _ ‹1 ≤ _ ∧ _›
    simp_all
  case vc4.h =>
    have hc := varint.lenOf_char _ _ ‹1 ≤ _ ∧ _›
    simp_all +zetaDelta
    scalar_tac
  case vc5.hQ => intro out h; cases h
  case vc6.hQ =>
    rename_i val2 ll hr cap v1 hrep back w hw u out2 out3 i hwr hout hne hv hcap hi1 hi2
    intro out h
    obtain rfl := core.result.Result.Ok.inj h
    have hc := varint.lenOf_char _ _ hr
    refine ⟨hv.2, ?_⟩
    have hpre := varint.write_prefix_content val2.val w.2.val (fun k => by
      have := hw.2.2 k
      rwa [hrep, hc.1] at this)
    have hlv : val2.val = self.vec.val.length := hv.1
    rw [hlv] at hpre
    rw [hout, List.map_append]
    exact congrArg (· ++ _) hpre
  case vc7.h_fail =>
    have hc := varint.lenOf_char _ _ ‹1 ≤ _ ∧ _›
    exfalso
    simp_all +zetaDelta [Slice.length]
  try_vcs
  all_goals (try (intros; simp [PostCond.ok]))

/-- `VLByteSlice::tls_serialize_bytes` on contents. -/
theorem quic_vec.VLByteSlice.serialize_content (self : quic_vec.VLByteSlice) :
    ⦃ ⌜ True ⌝ ⦄ quic_vec.VLByteSlice.Insts.Tls_codecSerializeBytes.tls_serialize_bytes self
    ⦃ ⇓ r => ⌜ ∀ out, r = .Ok out → self.val.length ≤ 2 ^ 30 - 1 ∧
        out.val.map (·.val) = varint.encList self.val.length ++ self.val.map (·.val) ⌝ ⦄ := by
  mvcgen [quic_vec.VLByteSlice.Insts.Tls_codecSerializeBytes.tls_serialize_bytes,
    quic_vec.ContentLength.Insts.Tls_codecSize.tls_serialized_len,
    varint.TlsVarInt.Insts.Tls_codecSize.tls_serialized_len,
    quic_vec.ContentLength.Insts.Tls_codecSerializeBytes.tls_serialize_bytes,
    varint.TlsVarInt.serialize_content, varint.TlsVarInt.serialize_len_char,
    alloc.vec.Vec.with_capacity, checked_alloc_len_small,
    alloc.vec.Vec.append, rust_primitives.sequence.seq_concat,
    alloc.vec.Vec.Insts.CoreIterTraitsCollectExtendSharedAT.extend_slice_spec]
  all_goals (try simp only [continue_eq_tryCF] at *)
  all_goals subst_vars
  all_goals (try simp only [Slice.len_val] at *)
  case vc1.h => rename_i hr hv; have := hr.2.1; omega
  case vc2.h =>
    rename_i val r hr _ v1 comb hcomb hv1 hv _
    obtain ⟨v, hv', hl⟩ := hv1
    cases hv'
    have hv2 : self.val.length ≤ 2 ^ 30 - 1 := hv.2
    have hlo : varint.lenOf val.val ≤ 8 := by unfold varint.lenOf; split_ifs <;> omega
    have := congrArg List.length hl
    simp only [comb, List.length_append, List.length_map, List.length_range, Slice.new,
      List.length_nil] at this ⊢
    scalar_tac
  case vc3 =>
    rename_i val r hr _ v1 out comb hcomb hout hv1 hv _
    obtain ⟨v, hv', hl⟩ := hv1
    cases hv'
    intro o h
    obtain rfl := core.result.Result.Ok.inj h
    refine ⟨hv.2, ?_⟩
    have hlv : val.val = self.val.length := hv.1
    rw [hout, List.map_append]
    simp only [comb, hl, varint.encList, hlv, Slice.new, List.nil_append]
  case vc4.hQ =>
    exfalso
    rename_i val r hr _ v1 comb hcomb hv1 hv _
    obtain ⟨v, hv', hl⟩ := hv1
    cases hv'
    have hv2 : self.val.length ≤ 2 ^ 30 - 1 := hv.2
    have hlo : varint.lenOf val.val ≤ 8 := by unfold varint.lenOf; split_ifs <;> omega
    have := congrArg List.length hl
    apply hcomb
    simp only [comb, List.length_append, List.length_map, List.length_range, Slice.new,
      List.length_nil] at this ⊢
    scalar_tac
  try_vcs
  all_goals (try (intros; simp [PostCond.ok]))

/-- Partial spec of the serialisation loop of the slice serializer, on contents: if it finishes
without error, the output grew by the concatenation of the element encodings `enc`. -/
theorem loop_ser_content_spec {T : Type} (enc : T → List Std.U8) (it : core.slice.iter.Iter T)
    (out : alloc.vec.Vec Std.U8)
    (body : core.slice.iter.Iter T × alloc.vec.Vec Std.U8 →
      RustM (ControlFlow (core.slice.iter.Iter T × alloc.vec.Vec Std.U8)
        (alloc.vec.Vec Std.U8 × core.option.Option Error)))
    (hbody : ∀ (it' : core.slice.iter.Iter T) (o : alloc.vec.Vec Std.U8),
      ⦃ ⌜ True ⌝ ⦄ body (it', o)
      ⦃ ⇓? r => ⌜ match r with
        | .done y => y.2 = core.option.Option.None → (it' : Slice T).val = [] ∧ y.1 = o
        | .cont p => ∃ e, (it' : Slice T).val = e :: (p.1 : Slice T).val ∧
            (p.2 : Slice Std.U8).val = (o : Slice Std.U8).val ++ enc e ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄ loop body (it, out)
    ⦃ ⇓? r => ⌜ r.2 = core.option.Option.None →
        (r.1 : Slice Std.U8).val = (out : Slice Std.U8).val ++ (it : Slice T).val.flatMap enc ⌝ ⦄ := by
  refine loop_partial_spec body (it, out)
    (fun p => ∃ lc, (it : Slice T).val = lc ++ (p.1 : Slice T).val ∧
      (p.2 : Slice Std.U8).val = (out : Slice Std.U8).val ++ lc.flatMap enc)
    _ ⟨[], by simp, by simp⟩ ?_
  rintro ⟨it', o⟩ ⟨lc, h1, h2⟩
  apply partial_triple_post_mono (hbody it' o)
  intro r hr
  cases r with
  | done y =>
    intro hy
    obtain ⟨h0, rfl⟩ := hr hy
    simp only at h1 h0 h2 ⊢
    rw [h1, h0, List.append_nil]; exact h2
  | cont p =>
    obtain ⟨e, hl, hp⟩ := hr
    refine ⟨lc ++ [e], ?_, ?_⟩
    · rw [h1, hl]; simp
    · rw [hp]; simp only at h2; rw [h2]; simp

/-- `mvcgen` on the unfolded slice serializer for the content specs (cf. `ser_slice_mvcgen`). -/
syntax "ser_slice_mvcgen_content" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| ser_slice_mvcgen_content [$ts,*]) => `(tactic| mvcgen [-Aeneas.Std.loop_spec, $ts,*,
    quic_vec.ContentLength.from_usize_spec, varint.TlsVarInt.bytes_len_spec,
    checked_alloc_len_ok, alloc.vec.Vec.with_capacity, alloc.vec.Vec.resize_U8_content,
    alloc.vec.Vec.Insts.CoreOpsDerefDerefMutSlice.deref_mut, alloc.vec.Vec.as_mut_slice,
    rust_primitives.sequence.seq_to_slice_mut, varint.TlsVarInt.write_bytes_content,
    core.slice.Slice.iter, core.iter.traits.collect.IntoIterator.Blanket.into_iter,
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
    alloc.vec.Vec.append, rust_primitives.sequence.seq_concat])

/-- The `<&[T]>::tls_serialize_bytes` on contents, given the contents `enc` of the element
serializer: an `Ok` output is the length prefix of the total size and the concatenation of the
elements. -/
theorem Shared0Slice.serialize_content {T : Type} (inst : SerializeBytes T)
    (enc : T → List Std.U8)
    (hs : ∀ x, ⦃ ⌜ True ⌝ ⦄ inst.tls_serialize_bytes x
      ⦃ ⇓? r => ⌜ ∀ b, r = .Ok b → (b : Slice Std.U8).val = enc x ⌝ ⦄) (s : Slice T) :
    ⦃ ⌜ True ⌝ ⦄ Shared0Slice.Insts.Tls_codecSerializeBytes.tls_serialize_bytes inst s
    ⦃ ⇓? r => ⌜ ∀ out, r = .Ok out → (s.val.flatMap enc).length ≤ 2 ^ 30 - 1 ∧
        out.val.map (·.val) = varint.encList (s.val.flatMap enc).length ++
          (s.val.flatMap enc).map (·.val) ⌝ ⦄ := by
  ser_slice_setup
  have hsum := loop_trivial_partial
    (α := core.slice.iter.Iter T × Std.Usize) (β := core.result.Result Std.Usize Error)
  have hser := loop_ser_content_spec enc
  ser_slice_mvcgen_content [hsum, hser, hs]
  all_goals (try clear hsum hser)
  try_vcs
  all_goals (try (intros; simp [PostCond.ok]; done))
  case vc1.hv => rename_i h; rw [h]; rfl
  case vc2.h =>
    have hc := varint.lenOf_char _ _ ‹1 ≤ _ ∧ _›
    rename_i hrep back
    rw [hrep, List.length_replicate]; omega
  case vc3.hQ => rw [← List.length_eq_zero_iff]; scalar_tac
  case vc4.hQ =>
    rename_i it' o hne hlt r bytes hbr hb comb hc
    refine ⟨(it' : Slice T).val.get ⟨0, by simpa using hlt⟩, ?_, ?_⟩
    · simp only [show (0#usize).val = 0 from rfl, List.take_zero, List.nil_append, zero_add]
      exact list_cons_get_drop _ ‹_›
    · simp [comb, hb bytes rfl]
  case vc6 => intro h; cases h
  case vc8 => intro out h; cases h
  case vc9.hQ => intro out h; cases h
  case vc10.hQ =>
    intro out h
    obtain rfl := core.result.Result.Ok.inj h
    simp only [continue_eq_tryCF] at *
    subst_vars
    rename_i acc2 val ll hll acc1 v1 hrep back w hw acc0 r1 hnone hr1 i hne hwr hv hcap hi1 hi2
    have hc := varint.lenOf_char _ _ hll
    have hpre := varint.write_prefix_content val.val w.2.val (fun k => by
      have := hw.2.2 k
      rwa [hrep, hc.1] at this)
    have hr1' := hr1 hnone
    have hwl : (w.2 : Slice Std.U8).val.length = ll.val := by
      rw [hw.2.1, hrep, List.length_replicate]
    have hlen : (r1.1 : Slice Std.U8).val.length = ll.val + (s.val.flatMap enc).length := by
      rw [hr1', List.length_append]
      show (w.2 : Slice Std.U8).val.length + _ = _
      rw [hwl]
    have hne' : i = acc2 := by simpa only [bne_iff_ne, ne_eq, not_not] using hne
    have hflat : (s.val.flatMap enc).length = acc2.val := by
      subst hne'
      rw [Slice.len_val] at hi1
      have : Slice.length (r1.1 : Slice Std.U8) = (r1.1 : Slice Std.U8).val.length := rfl
      omega
    have hvv : val.val = (s.val.flatMap enc).length := by rw [hflat]; exact hv.1
    refine ⟨by omega, ?_⟩
    rw [hr1', List.map_append, ← hvv]
    exact congrArg (· ++ _) hpre

/-- The `Vec<T>` serializer on contents (see `Shared0Slice.serialize_content`). -/
theorem alloc.vec.Vec.serialize_content {T : Type} (inst : SerializeBytes T) (enc : T → List Std.U8)
    (hs : ∀ x, ⦃ ⌜ True ⌝ ⦄ inst.tls_serialize_bytes x
      ⦃ ⇓? r => ⌜ ∀ b, r = .Ok b → (b : Slice Std.U8).val = enc x ⌝ ⦄) (v : alloc.vec.Vec T) :
    ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.Insts.Tls_codecSerializeBytes.tls_serialize_bytes inst v
    ⦃ ⇓? r => ⌜ ∀ out, r = .Ok out → ((v : Slice T).val.flatMap enc).length ≤ 2 ^ 30 - 1 ∧
        out.val.map (·.val) = varint.encList ((v : Slice T).val.flatMap enc).length ++
          ((v : Slice T).val.flatMap enc).map (·.val) ⌝ ⦄ := by
  rw [alloc.vec.Vec.ser_eq_slice]
  exact Shared0Slice.serialize_content inst enc hs _

theorem alloc.vec.Vec.deserialize_bytes_loop_body_content {T : Type} (inst : DeserializeBytes T)
    (enc : T → List Std.U8)
    (hd : ∀ b, ⦃ ⌜ True ⌝ ⦄ inst.tls_deserialize_bytes b
      ⦃ ⇓? r => ⌜ ∀ x t, r = .Ok (x, t) → (b : Slice Std.U8).val = enc x ++ t.val ⌝ ⦄)
    (length : Std.Usize) (result : alloc.vec.Vec T) (remainder : Slice Std.U8) (read : Std.Usize)
    (hinv : (result : Slice T).val.length ≤ read.val) :
    ⦃ ⌜ True ⌝ ⦄
    alloc.vec.Vec.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes_loop.body inst length
      remainder result read
    ⦃ ⇓? r => ⌜ match r with
      | .done (rem, res, rd, fl) => fl = core.option.Option.None →
          rem = remainder ∧ res = result ∧ rd = read
      | .cont (rem, res, rd) => ∃ x, remainder.val = enc x ++ rem.val ∧
          (res : Slice T).val = (result : Slice T).val ++ [x] ∧
          rd.val = read.val + (enc x).length ∧ (res : Slice T).val.length ≤ rd.val ⌝ ⦄ := by
  mvcgen [alloc.vec.Vec.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes_loop.body, hd,
    core.convert.Into.Blanket.into]
  case vc1.h => rename_i hlt _ _ _ _ _ _ _ _ _ _; scalar_tac
  case vc2.h => exact toStr_utf8 _ _
  case vc3 => intro h; cases h
  case vc4.hQ =>
    rename_i hlt r p hx hpost r2 h2 r1 h1 r0 ha hb res hnz hpush rd hrd
    obtain ⟨e, nxt⟩ := p
    have hr := hpost e nxt rfl
    subst h2 h1
    have l1 := Slice.len_val remainder
    have l2 := Slice.len_val nxt
    simp only [Slice.length] at l1 l2
    have hnz' : r0.val ≠ 0 := fun h => hnz (UScalar.eq_of_val_eq (by simpa using h))
    have hlen : r0.val = (enc e).length := by
      have := congrArg List.length hr; simp only [List.length_append] at this; dsimp only at *; omega
    refine ⟨e, hr, hpush, by dsimp only at *; omega, ?_⟩
    rw [hpush]; simp; dsimp only at *; omega
  case vc7 => intro h; cases h

theorem alloc.vec.Vec.deserialize_bytes_loop_content {T : Type} (inst : DeserializeBytes T)
    (enc : T → List Std.U8)
    (hd : ∀ b, ⦃ ⌜ True ⌝ ⦄ inst.tls_deserialize_bytes b
      ⦃ ⇓? r => ⌜ ∀ x t, r = .Ok (x, t) → (b : Slice Std.U8).val = enc x ++ t.val ⌝ ⦄)
    (length : Std.Usize) (remainder : Slice Std.U8) (result : alloc.vec.Vec T) (read : Std.Usize)
    (hres : (result : Slice T).val = []) (hread : read.val = 0) :
    ⦃ ⌜ True ⌝ ⦄
    alloc.vec.Vec.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes_loop inst remainder length
      result read
    ⦃ ⇓? r => ⌜ r.2.2.2 = core.option.Option.None →
        remainder.val = (r.2.1 : Slice T).val.flatMap enc ++ r.1.val ∧
        r.2.2.1.val = ((r.2.1 : Slice T).val.flatMap enc).length ⌝ ⦄ := by
  unfold alloc.vec.Vec.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes_loop
  refine loop_partial_spec _ (remainder, result, read)
    (fun p => remainder.val = (p.2.1 : Slice T).val.flatMap enc ++ p.1.val ∧
      p.2.2.val = ((p.2.1 : Slice T).val.flatMap enc).length ∧
      (p.2.1 : Slice T).val.length ≤ p.2.2.val)
    _ ⟨by simp [hres], by simp [hres, hread], by simp [hres]⟩ ?_
  rintro ⟨rem, res, rd⟩ ⟨h1, h2, h3⟩
  dsimp only at h1 h2 h3
  apply partial_triple_post_mono
    (alloc.vec.Vec.deserialize_bytes_loop_body_content inst enc hd length res rem rd h3)
  intro r hr
  cases r with
  | done y =>
    obtain ⟨rem', res', rd', fl⟩ := y
    intro hfl
    obtain ⟨rfl, rfl, rfl⟩ := hr hfl
    exact ⟨h1, h2⟩
  | cont p =>
    obtain ⟨rem', res', rd'⟩ := p
    obtain ⟨x, hx, hres', hrd, hlen⟩ := hr
    refine ⟨?_, ?_, hlen⟩
    · simp only [hres', List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.append_assoc]
      rw [h1, hx]
    · simp only [hres', List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.length_append]
      omega

/-- The `Vec<T>` deserializer on contents, given the contents `enc` of the element deserializer:
on success the input is the length prefix of the total size, the concatenated elements and the
remainder. -/
theorem alloc.vec.Vec.deserialize_bytes_content {T : Type} (inst : DeserializeBytes T)
    (enc : T → List Std.U8)
    (hd : ∀ b, ⦃ ⌜ True ⌝ ⦄ inst.tls_deserialize_bytes b
      ⦃ ⇓? r => ⌜ ∀ x t, r = .Ok (x, t) → (b : Slice Std.U8).val = enc x ++ t.val ⌝ ⦄)
    (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes inst bytes
    ⦃ ⇓? r => ⌜ ∀ v t, r = .Ok (v, t) → ((v : Slice T).val.flatMap enc).length ≤ 2 ^ 30 - 1 ∧
        bytes.val.map (·.val) = varint.encList ((v : Slice T).val.flatMap enc).length ++
          ((v : Slice T).val.flatMap enc).map (·.val) ++ t.val.map (·.val) ⌝ ⦄ := by
  have hl := alloc.vec.Vec.deserialize_bytes_loop_content inst enc hd
  mvcgen [alloc.vec.Vec.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes,
    quic_vec.ContentLength.deserialize_content, varint.TlsVarInt.value, hl,
    alloc.vec.Vec.new_spec, core.hint.must_use_spec]
  try_vcs
  all_goals (try simp only [continue_eq_tryCF] at *)
  all_goals (try (intro _ _ h; cases h; done))
  all_goals (try (intros; simp [PostCond.ok]; done))
  case vc1 =>
    rename_i r0 hP r1 p x1 r2 htf r3 val x2 hv0 rv hrv h3 h5
    intro v t h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (core.result.Result.Ok.inj h)
    have hp := hP p.1 p.2 h3
    have hy := htf.1 val h5
    have hv : val.val = 0 := by rw [hv0]; rfl
    have hrl : rv.val = [] := by rw [hrv]; simp [Slice.new]
    refine ⟨by simp [hrl], ?_⟩
    rw [hp.2]
    simp [hrl, show p.1.val = 0 by omega]
  case vc2.hres => subst_vars; rfl
  case vc5 =>
    rename_i r0 hP r1 p x1 r2 htf r3 val x2 hnz rv hrv res hnone hne hpost hr0 hr2
    intro v t h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (core.result.Result.Ok.inj h)
    have hp := hP p.1 p.2 hr0
    have hy := htf.1 val hr2
    obtain ⟨hrem, hrd⟩ := hpost hnone
    have hrv' : res.2.2.1.val = val.val := by simpa using hne
    have hlen : ((res.2.1 : Slice T).val.flatMap enc).length = p.1.val := by omega
    refine ⟨le_of_eq_of_le hlen hp.1, ?_⟩
    rw [hp.2, hlen, hrem, List.map_append, List.append_assoc]


/-- The prefix of `b` is `out`, when the contents (as naturals) agree. -/
theorem list_take_of_map (b out : List Std.U8) (E R : List Nat) (c : Nat)
    (hb : b.map (·.val) = E ++ R) (ho : out.map (·.val) = E) (hc : c = E.length) :
    b.take c = out := by
  apply List.map_injective_iff.mpr (fun a b h => UScalar.eq_of_val_eq h)
  rw [List.map_take, hb, hc, List.take_left, ho]

/-- The big-endian encoding of a `u16`. -/
def u16Enc (x : Std.U16) : List Std.U8 := (Aeneas.Std.core.num.U16.to_be_bytes x).val

theorem u16Enc_length (x : Std.U16) : (u16Enc x).length = 2 := by
  simpa [u16Enc] using (Aeneas.Std.core.num.U16.to_be_bytes x).property

theorem u16Enc_inj {x y : Std.U16} (h : u16Enc x = u16Enc y) : x = y := by
  rw [← U16_from_be_bytes_to_be_bytes x, ← U16_from_be_bytes_to_be_bytes y]
  exact congrArg _ (Subtype.ext h)

/-- The concatenated big-endian encodings determine the list of `u16`. -/
theorem u16Enc_flatMap_inj : ∀ (l l' : List Std.U16), l.flatMap u16Enc = l'.flatMap u16Enc → l = l'
  | [], [], _ => rfl
  | [], y :: ys, h => by
    have := congrArg List.length h
    simp [u16Enc_length] at this
  | x :: xs, [], h => by
    have := congrArg List.length h
    simp [u16Enc_length] at this
  | x :: xs, y :: ys, h => by
    simp only [List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by rw [u16Enc_length, u16Enc_length])
    rw [u16Enc_inj h1, u16Enc_flatMap_inj xs ys h2]

/-- The element serializer of `u16`, on contents (partial form, for `Vec::serialize_content`). -/
theorem U16.serialize_content_partial (x : Std.U16) :
    ⦃ ⌜ True ⌝ ⦄ U16.Insts.Tls_codecSerializeBytes.tls_serialize_bytes x
    ⦃ ⇓? r => ⌜ ∀ b, r = .Ok b → (b : Slice Std.U8).val = u16Enc x ⌝ ⦄ := by
  apply partial_of_total
  apply triple_post_mono (U16_serialize_char x)
  rintro r ⟨v, rfl, hv⟩ b hb
  obtain rfl := core.result.Result.Ok.inj hb
  exact hv

/-- The element deserializer of `u16`, on contents (partial form). -/
theorem U16.deserialize_content_partial (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ U16.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes bytes
    ⦃ ⇓? r => ⌜ ∀ x t, r = .Ok (x, t) → bytes.val = u16Enc x ++ t.val ⌝ ⦄ := by
  apply partial_of_total
  apply triple_post_mono (U16_deserialize_char bytes)
  intro r hr x t hxt
  by_cases hl : 2 ≤ bytes.val.length
  · obtain ⟨a, t', ha, ht', rfl⟩ := hr.1 hl
    obtain ⟨hx, rfl⟩ := Prod.mk.inj (core.result.Result.Ok.inj hxt)
    subst hx
    rw [u16Enc, U16_to_be_bytes_from_be_bytes, ha, ht', List.take_append_drop]
  · rw [hr.2 (by omega)] at hxt
    cases hxt


/-- Round trip of a length-prefixed payload: if a serialized `A` (prefix of its length) is read as a
payload `B` followed by `R`, then `A = B` and nothing is left. -/
theorem varint.enc_roundtrip (A B R : List Std.U8) (hn : A.length ≤ 2 ^ 30 - 1)
    (hn' : B.length ≤ 2 ^ 30 - 1)
    (h : varint.encList A.length ++ A.map (·.val) =
      varint.encList B.length ++ B.map (·.val) ++ R.map (·.val)) : A = B ∧ R = [] := by
  rw [List.append_assoc] at h
  obtain ⟨hlen, happ⟩ := varint.encList_append_inj _ _ _ _ (by omega) (by omega) h
  have hR : R.length = 0 := by
    have := congrArg List.length happ
    simp only [List.length_append, List.length_map] at this
    omega
  have hR' : R = [] := List.length_eq_zero_iff.mp hR
  refine ⟨?_, hR'⟩
  apply List.map_injective_iff.mpr (fun a b h => UScalar.eq_of_val_eq h)
  rw [happ, hR', List.map_nil, List.append_nil]


/-- The `String` as a slice of its UTF-8 bytes, when that slice is short, is the whole encoding. -/
theorem alloc.string.String.take_max_utf8U8 (s : alloc.string.String)
    (h : ((alloc.string.String.utf8U8 s).take Usize.max).length ≤ 2 ^ 30 - 1) :
    (alloc.string.String.utf8U8 s).take Usize.max = alloc.string.String.utf8U8 s := by
  apply List.take_of_length_le
  by_contra hc
  rw [List.length_take] at h
  have : 2 ^ 30 - 1 < Usize.max := by scalar_tac
  omega

/-- `String::tls_serialize_bytes` on contents: the length prefix and the UTF-8 bytes. -/
theorem alloc.string.String.serialize_content (s : alloc.string.String) :
    ⦃ ⌜ True ⌝ ⦄ alloc.string.String.Insts.Tls_codecSerializeBytes.tls_serialize_bytes s
    ⦃ ⇓ r => ⌜ ∀ out, r = .Ok out → (alloc.string.String.utf8U8 s).length ≤ 2 ^ 30 - 1 ∧
        out.val.map (·.val) = varint.encList (alloc.string.String.utf8U8 s).length ++
          (alloc.string.String.utf8U8 s).map (·.val) ⌝ ⦄ := by
  mvcgen [alloc.string.String.Insts.Tls_codecSerializeBytes.tls_serialize_bytes,
    alloc.string.String.as_bytes_spec, quic_vec.VLByteSlice.serialize_content]
  rename_i b hb r
  intro h out hr
  obtain ⟨hl, hc⟩ := h out hr
  rw [hb] at hl hc
  have ht := alloc.string.String.take_max_utf8U8 s hl
  rw [ht] at hl hc
  exact ⟨hl, hc⟩

/-- `String::tls_deserialize_bytes` on contents: the length prefix, the UTF-8 bytes of the string and
the remainder. -/
theorem alloc.string.String.deserialize_content (bytes : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ alloc.string.String.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes bytes
    ⦃ ⇓ r => ⌜ ∀ t rem, r = .Ok (t, rem) →
        (alloc.string.String.utf8U8 t).length ≤ 2 ^ 30 - 1 ∧ bytes.val.map (·.val) =
          varint.encList (alloc.string.String.utf8U8 t).length ++
            (alloc.string.String.utf8U8 t).map (·.val) ++ rem.val.map (·.val) ⌝ ⦄ := by
  apply triple_post_mono (alloc.string.String.deserialize_char bytes)
  intro r h t rem hr
  obtain ⟨raw, hraw, hu⟩ := h t rem hr
  obtain ⟨r0, hr0, hP⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp
    (quic_vec.VLByteVec.deserialize_content bytes)
  rw [hraw] at hr0
  cases hr0
  rw [hu]
  exact hP raw rem rfl

end tls_codec
