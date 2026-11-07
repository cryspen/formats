/- `mvcgen` on universe-polymorphic extracted code.

The extracted generics are `{T : Type _}`, so a program over `T` binds computations living in
different universes (`let l ← seq_len v` returns a `Usize : Type`, the program a
`Vec T : Type u`): `Aeneas.Std.bind {α : Type u} {β : Type v}`. `Std.Do` triples are about one
monad `RustM.{v}`, so `mvcgen` cannot step through such a bind: it stops and leaves the whole
program as a VC. Two fixes, global for every proof importing this module:

1. `Aeneas.Std.bind_spec_same` (`@[spec]`): `Spec.bind` for a same-universe `Std.bind` (the
   built-in handling of `Std.bind` fires at `Type` only).
2. `Aeneas.Std.bind_spec_hetero` (`@[spec low]`): a cross-universe bind has the precondition
   `⌜RustM.wpDown x Q'⌝`, i.e. the weakest precondition of `x` (at `x`'s universe) for the
   post "`RustM.wpDown (f a) Q`". `mvcgen` leaves it as a VC `RustM.wpDown x Q'`; the
   `mvcgen` elaborator below re-runs `mvcgen` (same lemmas, `-leave`, no invariant / VC
   alternatives) on every such VC and leaves its VCs itself (`leaveVC`: spec posts stay one
   hypothesis, `ExceptConds.false` leftovers become `False`), so one `mvcgen` call still goes
   through the whole program, with the same VCs as at `Type`.
-/
import Lean
import Aeneas
open Lean Elab Tactic Meta Std.Do Aeneas Aeneas.Std

namespace Aeneas.Std

/-- `x`'s weakest precondition, as a `Prop`: marks the VCs `mvcgen` must continue on. -/
def RustM.wpDown {α : Type u} (x : RustM α) (Q : PostCond α RustM.postShape) : Prop :=
  (wp⟦x⟧ Q).down

/-- Same-universe bind: `Spec.bind` for `Std.bind` (a wp-form precondition, which `mvcgen`
    keeps stepping through). Default priority, so it wins over `bind_spec_hetero`. -/
@[spec]
theorem bind_spec_same {α β : Type u} {x : RustM α} {f : α → RustM β}
    {Q : PostCond β RustM.postShape} :
    ⦃ wp⟦x⟧ (fun a => wp⟦f a⟧ Q, Q.2) ⦄ Aeneas.Std.bind x f ⦃ Q ⦄ :=
  Spec.bind

/-- Cross-universe bind. -/
@[spec low]
theorem bind_spec_hetero {α : Type u} {β : Type v} {x : RustM α} {f : α → RustM β}
    {Q : PostCond β RustM.postShape} :
    ⦃ ⌜ RustM.wpDown x (fun a => ⌜RustM.wpDown (f a) Q⌝, fun e => ⌜(Q.2.1 ⟨e.down⟩).down⌝,
        fun _ => ⌜(Q.2.2.1 ⟨⟩).down⌝, fun _ => ⌜(Q.2.2.2.1 ⟨⟩).down⌝, ⟨⟩) ⌝ ⦄
    Aeneas.Std.bind x f ⦃ Q ⦄ := by
  cases x with
  | ret a => simp [Triple, RustM.wpDown, WP.wp, PredTrans.apply]
  | vis i k => cases i; simp [Triple, RustM.wpDown, WP.wp, PredTrans.apply]
  | div => simp [Triple, RustM.wpDown, WP.wp, PredTrans.apply]

end Aeneas.Std

namespace TlsCodec.MvcgenUniv

/-- Leave a VC of a nested (`-leave`) `mvcgen` run: `h : ⌜P⌝ ⊢ₛ ⌜C⌝` becomes `P → C` with `P`
    kept whole (the built-in `mleave` would split `P = A ∧ B` / `∃ x, …` into several
    hypotheses, unlike the hypotheses of a direct `mvcgen` run); anything else: `mleave`. -/
def leaveVC (g : MVarId) : TacticM (List MVarId) := do
  evalTacticAt (← `(tactic| first
    | (mstop; simp only [SPred.entails_nil, SPred.down_pure, SPred.and_nil, true_implies,
        ExceptConds.fst_false, ExceptConds.snd_false])
    | mleave
    | skip)) g

/-- Continue `mvcgen` on a `wpDown` VC (after introducing its hypotheses, as `mvcgen` does):
    `stx` is the `mvcgen` call, with `-leave` and without invariant / VC alternatives. -/
partial def continueAt (stx : Syntax) (g : MVarId) : TacticM (List MVarId) := do
  let isWpDown ← g.withContext do forallTelescope (← instantiateMVars (← g.getType)) fun _ b =>
    return b.isAppOf ``Aeneas.Std.RustM.wpDown
  unless isWpDown do return [g]
  let (_, g) ← g.intros
  g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let some ty' ← unfoldDefinition? ty | return [g]
  let g' ← g.replaceTargetDefEq ty'
  let gs ← withOptions (·.setBool `linter.deprecated.syntax false) (evalTacticAt stx g')
  gs.flatMapM fun g => do (← leaveVC g).flatMapM (continueAt stx)

/-- `mvcgen`, then `continueAt` on its VCs (tried before the built-in elaborator). -/
@[tactic Lean.Parser.Tactic.mvcgen]
def elabMvcgenUniv : Tactic := fun stx => do
  Lean.Elab.Tactic.Do.elabMVCGen stx
  let cfg ← `(Lean.Parser.Tactic.optConfig| -leave)
  let stx' := ((stx.setArg 1 cfg).setArg 3 mkNullNode).setArg 4 mkNullNode
  let goals ← getGoals
  setGoals (← goals.flatMapM (continueAt stx'))

end TlsCodec.MvcgenUniv
