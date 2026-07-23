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
  return nonexpExt.getState env

elab "nonexp" : tactic => do
  let lemmas := (← nonexpLemmas).reverse
  for lem in lemmas do
    let lemmaIdent := mkIdent lem
    try
      let tac ← `(tactic|apply $lemmaIdent:ident; try intros)
      evalTactic tac
      return
    catch _ =>
      continue

elab "contractive" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let lemmaIdent := mkIdent ``OFE.Contractive.distLater_dist
    try
      let tac ← `(tactic|apply $lemmaIdent:ident; intro _ _)
      evalTactic tac
      return
    catch _ =>
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
