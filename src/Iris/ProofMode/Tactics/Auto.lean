/-
Copyright (c) 2025 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.Std
import Iris.ProofMode.Tactics.Basic

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

variable {prop : Q(Type u)} (bi : Q(BI $prop)) in
partial def iAutoCore
    {e} (hyps : Hyps bi e) (goal : Q($prop))
    (k : ∀ {e}, Hyps bi e → (goal : Q($prop)) → MetaM Q($e ⊢ $goal)) :
    MetaM (Q($e ⊢ $goal)) := do
  if let some inst ← try? <| synthInstanceQ q(AutoSolve $e $goal) then
    return q(($inst).solution)
  else
    throwError "iauto: failed"

elab "iauto" : tactic => do
  let (mvar, { prop, bi, hyps, goal, .. }) ← istart (← getMainGoal)

  mvar.withContext do
    let goals ← IO.mkRef #[]
    let pf ← iAutoCore bi hyps goal fun {P} hyps goal => do
      let m : Q($P ⊢ $goal) ← mkFreshExprSyntheticOpaqueMVar <|
        IrisGoal.toExpr { prop, bi, hyps, goal, .. }
      goals.modify (·.push m.mvarId!)
      pure m

    mvar.assign pf
    replaceMainGoal (← goals.get).toList
