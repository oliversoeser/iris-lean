/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.ProofMode.Auto.Instances
import Iris.ProofMode.Tactics.Basic
import Iris.ProofMode.Tactics.Remove

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std


elab "iauto" : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
    let g ← instantiateMVars <| ← mvar.getType
    let some { prop, bi, e, hyps, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"
    logInfo e
    logInfo goal
