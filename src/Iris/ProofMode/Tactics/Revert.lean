/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.ProofMode.Tactics.Cases

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

elab "irevert" colGt hyp:ident : tactic => do
  let (mvar, { u, prop, bi, e, hyps, goal, .. }) ← istart (← getMainGoal)

  mvar.withContext do
    let uniq ← hyps.findWithInfo hyp
    let ⟨e', hyps', _, _, _, _, _⟩ := hyps.remove true uniq
    let m : Q($e' ⊢ $e -∗ $goal) ← mkFreshExprSyntheticOpaqueMVar <|
      IrisGoal.toExpr { u, prop, bi, hyps := hyps', goal := ← mkAppM ``BIBase.wand #[e, goal], .. }

    let pf : Q($e ⊢ $goal) ← mkAppM ``wand_elim #[m]
    mvar.assign pf
    replaceMainGoal [m.mvarId!]

#check wand_entails
#check wand_elim
