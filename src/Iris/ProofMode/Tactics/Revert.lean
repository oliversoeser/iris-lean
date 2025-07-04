/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.ProofMode.Tactics.Cases

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

theorem wand_revert [BI PROP] {P Q A1 A2 : PROP}
    (h1 : P ⊣⊢ A1 ∗ A2) (h2 : A1 ⊢ A2 -∗ Q) : P ⊢ Q :=
  h1.mp.trans (wand_elim h2)

theorem forall_revert [BI PROP] {P : PROP} {Ψ : α → PROP}
    (h : P ⊢ ∀ x, Ψ x) : ∀ x, P ⊢ Ψ x :=
  λ x => h.trans (forall_elim x)

elab "irevert" colGt hyp:ident : tactic => do
  let (mvar, { u, prop, bi, e, hyps, goal, .. }) ← istart (← getMainGoal)

  mvar.withContext do
    -- checks if the identifier exists in the iris context
    let uniq? ← try? do Pure.pure (← hyps.findWithInfo hyp)
    if let (some uniq) := uniq? then
      let ⟨e', hyps', out, _, _, _, h⟩ := hyps.remove true uniq
      let m : Q($e' ⊢ $out -∗ $goal) ← mkFreshExprSyntheticOpaqueMVar <|
        IrisGoal.toExpr { hyps := hyps', goal := q(wand $out $goal), .. }

      let pf : Q($e ⊢ $goal) := q(wand_revert $h $m)

      mvar.assign pf
      replaceMainGoal [m.mvarId!]
    else
      let f ← getFVarId hyp
      let lctx ← getLCtx
      let (some ldecl) := (lctx.find? f) | throwError "given identifier does not exist in context"

      -- todo: case for Prop
      let αType := ldecl.type
      if ← Meta.isProp αType then
        let (_, mvarId) ← mvar.revert #[f]
        mvarId.withContext do
          logInfo (← mvarId.getType)
      else
        let v ← Meta.getLevel αType
        let (_, mvarId) ← mvar.revert #[f]
        mvarId.withContext do
          let Φ ← mapForallTelescope' (λ t _ => do
            let (some ig) := parseIrisGoal? t | throwError "failed to parse iris goal"
            return ig.goal
          ) (Expr.mvar mvarId)
          let m ← mkFreshExprSyntheticOpaqueMVar <|
            IrisGoal.toExpr { u, prop, bi, hyps, goal := mkAppN (mkConst ``BI.forall [u, v]) #[prop, mkAppN (mkConst ``BI.toBIBase [u]) #[prop, bi], αType, Φ], ..}

          let pf := mkAppN (mkConst ``forall_revert [u, v]) #[prop, αType, bi, e, Φ, m]

          mvarId.assign pf
          replaceMainGoal [m.mvarId!]
