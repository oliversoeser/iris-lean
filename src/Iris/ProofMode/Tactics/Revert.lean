/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.ProofMode.Tactics.Cases

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

theorem wand_revert_spatial [BI PROP] {P Q A1 A2 : PROP}
    [h1 : IntoSep P A1 A2] [h2 : IntoWand false false A1 A2 Q] : P ⊢ Q :=
  h1.1.trans (wand_elim h2.1)

theorem forall_revert [BI PROP] {P : PROP} {Ψ : α → PROP}
    [h : IntoForall P Ψ] : ∀ a, P ⊢ Ψ a :=
  λ a => h.1.trans (forall_elim a)

elab "irevert" colGt hyp:ident : tactic => do
  let (mvar, { u, prop, bi, e, hyps, goal, .. }) ← istart (← getMainGoal)

  mvar.withContext do
    -- checks if the identifier exists in the iris context
    let uniq? ← try? do Pure.pure (← hyps.findWithInfo hyp)
    if let (some uniq) := uniq? then
      let ⟨e', hyps', out, _, _, _, h⟩ := hyps.remove true uniq
      let m : Q($e' ⊢ $out -∗ $goal) ← mkFreshExprSyntheticOpaqueMVar <|
        IrisGoal.toExpr { hyps := hyps', goal := q(wand $out $goal), .. }

      let _ : Q(IntoSep $e $e' $out) := q(IntoSep.mk (BIBase.BiEntails.mp $h))
      let _ : Q(IntoWand false false $e' $out $goal) := q(IntoWand.mk $m)

      let pf : Q($e ⊢ $goal) := q(wand_revert_spatial)

      mvar.assign pf
      replaceMainGoal [m.mvarId!]
    else
      let f ← getFVarId hyp
      let lctx ← getLCtx
      let (some ldecl) := (lctx.find? f) | throwError "given identifier does not exist in context"
      let α : Q(Type) := q(Nat) -- problem 1: type is hardcoded
      let Φ : Q($α → $prop) := q(fun _ => $goal)

      let m : Q($e ⊢ ∀ (_ : $α), $goal) ← mkFreshExprSyntheticOpaqueMVar <|
        IrisGoal.toExpr { u, prop, bi, hyps, goal := q(BIBase.forall $Φ), ..}

      let (_, mvarId) ← mvar.revert #[f] -- problem 2: f is removed from the context here, but this does not last

      let _ : Q(IntoForall $e $Φ) := q(IntoForall.mk $m)

      let pf : Q(∀ (_ : $α), $e ⊢ $goal) := q(forall_revert)

      mvarId.assign pf
      replaceMainGoal [m.mvarId!]
