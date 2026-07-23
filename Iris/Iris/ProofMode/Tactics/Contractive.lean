/-
Copyright (c) 2026 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
module

public meta import Iris.Algebra.OFE

namespace Iris.ProofMode

open Lean Elab Tactic Meta Iris.Std

meta def nonexpLemmas : MetaM (Array Name) := do
  let env ← getEnv
  return (nonexpExt.getState env).reverse

meta def distIsForall (expr : Expr) : MetaM Bool := do
  expr.withApp <| λ _ distArgs =>
    distArgs[1]!.withApp <| λ ofeFn _ => do
      return ofeFn.getLambdaBody.getAppFn.isConstOf ``OFE.instForallOfOFEFun

meta def nonexpStep : TacticM Bool := do
  for neLem in ← nonexpLemmas do
    try
      let tac ← `(tactic|apply $(mkIdent neLem):ident; try intros)
      evalTactic tac
      return true
    catch _ =>
      continue
  return false

meta def distInstanceStep : TacticM Bool := do
  try
    let tac ← `(tactic|apply $(mkIdent ``OFE.Contractive.distLater_dist); intro _ _)
    evalTactic tac
    return true
  catch _ =>
    return false

meta def distHypStep : TacticM Bool := do
  try
    let goal ← getMainGoal
    goal.withContext do
      let ctx ← getLCtx
      for decl? in ctx.decls do
        if let some decl := decl? then
          if decl.type.isAppOf ``OFE.DistLater then
            let declIdent := mkIdent decl.userName
            try
              let tac ← `(tactic|apply $declIdent:ident; assumption)
              evalTactic tac
              return
            catch _ =>
              continue
      throwError "unable to find matching DistLater hypothesis"
    return true
  catch _ => return false

elab "contractive" : tactic => do
  -- intro hypotheses
  evalTactic <| ← `(tactic|intros)

  -- intro foralls within OFE.Dist
  while ← distIsForall <| ← getMainTarget do
    evalTactic <| ← `(tactic|intro)

  -- unfold function definition, if possible
  let _ ← observing? ((← getMainTarget).withApp <| λ _ gArgs => do
    evalTactic <| ← `(tactic|unfold $(mkIdent gArgs[3]!.getAppFn.constName!); try split))

  -- main loop
  while ¬(← getUnsolvedGoals).isEmpty do
    -- simplification step (applies Dist.rfl)
    if let some _ ← observing? (evalTactic <| ← `(tactic|simp)) then continue

    let goal ← getMainGoal
    let goalType ← goal.getType
    dbg_trace goalType

    -- uses a OFE.Contractive instance, if available
    if ← distInstanceStep then continue

    -- applies a OFE.DistLater hypothesis
    if ← distHypStep then continue

    -- applies a non-expansive lemma
    if ← nonexpStep then continue

    -- exit if all fail
    break
