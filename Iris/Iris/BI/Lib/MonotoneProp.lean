/-
Copyright (c) 2026 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
module

public import Iris.BI.Lib.Fixpoint

@[expose] public section

namespace Iris
open BI OFE

structure BIMonoProp [BI PROP] (F : PROP → PROP) where
  mono_prop {P Q : PROP} : ⊢ □ (P -∗ Q) -∗ F P -∗ F Q

structure BIAntiProp [BI PROP] (F : PROP → PROP) where
  anti_prop {P Q : PROP} : ⊢ □ (P -∗ Q) -∗ F Q -∗ F P

section monotone

theorem monotone_const [BI PROP] (R : PROP) : BIMonoProp (λ_ => R) where
  mono_prop {P Q} := by
    iintro - HR
    iexact HR

theorem monotone_id [BI PROP] : BIMonoProp (λR : PROP => R) where
  mono_prop {P Q} := by
    iintro #H
    iexact H

theorem monotone_comp [BI PROP] (F G : PROP → PROP) (hf : BIMonoProp F)
    (hg : BIMonoProp G) : BIMonoProp (λP : PROP => F (G P)) where
  mono_prop {P Q} := by
    iintro #H
    iapply @hf.mono_prop (G P)
    imodintro
    iapply @hg.mono_prop
    iexact H

theorem monotone_comp' [BI PROP] (F G : PROP → PROP) (hf : BIAntiProp F)
    (hg : BIAntiProp G) : BIMonoProp (λP : PROP => F (G P)) where
  mono_prop {P Q} := by
    iintro #H
    iapply @hf.anti_prop (G Q)
    imodintro
    iapply @hg.anti_prop
    iexact H

-- TODO: monotone_pure

theorem monotone_and [BI PROP] (F G : PROP → PROP) (hf : BIMonoProp F)
    (hg : BIMonoProp G) : BIMonoProp (λP : PROP => iprop(F P ∧ G P)) where
  mono_prop {P Q} := by
    iintro #H1 H2
    isplit
    · iapply @hf.mono_prop P Q
      · iexact H1
      · iexact H2
    · iapply @hg.mono_prop P Q
      · iexact H1
      · iexact H2

theorem monotone_or [BI PROP] (F G : PROP → PROP) (hf : BIMonoProp F)
    (hg : BIMonoProp G) : BIMonoProp (λP : PROP => iprop(F P ∨ G P)) where
  mono_prop {P Q} := by
    iintro #H1 (HF | HG)
    · ileft
      iapply @hf.mono_prop P Q
      iexact H1
      iexact HF
    · iright
      iapply @hg.mono_prop P Q
      iexact H1
      iexact HG

-- TODO: monotone_imp

theorem monotone_forall [BI PROP] (F : A → PROP → PROP)
    (hf : ∀x, BIMonoProp (F x)) : BIMonoProp (λP : PROP => iprop(∀x, F x P)) where
  mono_prop {P Q} := by
    iintro #H1 H2 %a
    iapply @(hf a).mono_prop P
    · iexact H1
    · iexact H2

theorem monotone_exists [BI PROP] (F : A → PROP → PROP)
    (hf : ∀x, BIMonoProp (F x)) : BIMonoProp (λP : PROP => iprop(∃x, F x P)) where
  mono_prop {P Q} := by
    iintro #H1 ⟨%x, H2⟩
    iexists x
    iapply @(hf x).mono_prop P
    · iexact H1
    · iexact H2

theorem monotone_sep [BI PROP] (F G : PROP → PROP) (hf : BIMonoProp F)
    (hg : BIMonoProp G) : BIMonoProp (λP : PROP => iprop(F P ∗ G P)) where
  mono_prop {P Q} := by
    iintro #H1 ⟨HF, HG⟩
    isplitl [HF]
    · iapply @hf.mono_prop P Q
      · iexact H1
      · iexact HF
    · iapply @hg.mono_prop P Q
      · iexact H1
      · iexact HG

theorem monotone_wand [BI PROP] (F G : PROP → PROP) (hf : BIAntiProp F)
    (hg : BIMonoProp G) : BIMonoProp (λP : PROP => iprop(F P -∗ G P)) where
  mono_prop {P Q} := by
    iintro #H1 H2 HF
    iapply @hg.mono_prop P
    · iexact H1
    · iapply H2
      iapply @hf.anti_prop P Q
      · iexact H1
      · iexact HF

theorem monotone_persistently [BI PROP] (F : PROP → PROP) (hf : BIMonoProp F)
    : BIMonoProp (λP : PROP => iprop(<pers> F P)) where
  mono_prop {P Q} := by
    iintro #H1 #HF
    imodintro
    iapply @hf.mono_prop P Q
    · iexact H1
    · iexact HF

theorem monotone_later [BI PROP] (F : PROP → PROP) (hf : BIMonoProp F)
    : BIMonoProp (λP : PROP => iprop(▷ F P)) where
  mono_prop {P Q} := by
    iintro #H1 HP
    inext
    iapply @hf.mono_prop P Q
    · iexact H1
    · iexact HP

end monotone

section antitone

theorem antitone_const [BI PROP] (R : PROP) : BIAntiProp (λ_ => R) where
  anti_prop {P Q} := by
    iintro - HR
    iexact HR

theorem antitone_comp [BI PROP] (F G : PROP → PROP) (hf : BIAntiProp F)
    (hg : BIMonoProp G) : BIAntiProp (λP : PROP => F (G P)) where
  anti_prop {P Q} := by
    iintro #H
    iapply @hf.anti_prop (G P)
    imodintro
    iapply @hg.mono_prop
    iexact H

theorem antitone_comp' [BI PROP] (F G : PROP → PROP) (hf : BIMonoProp F)
    (hg : BIAntiProp G) : BIAntiProp (λP : PROP => F (G P)) where
  anti_prop {P Q} := by
    iintro #H
    iapply @hf.mono_prop (G Q)
    imodintro
    iapply @hg.anti_prop
    iexact H

-- TODO: antitone_pure

theorem antitone_and [BI PROP] (F G : PROP → PROP) (hf : BIAntiProp F)
    (hg : BIAntiProp G) : BIAntiProp (λP : PROP => iprop(F P ∧ G P)) where
  anti_prop {P Q} := by
    iintro #H1 H2
    isplit
    · iapply @hf.anti_prop P Q
      · iexact H1
      · iexact H2
    · iapply @hg.anti_prop P Q
      · iexact H1
      · iexact H2

theorem antitone_or [BI PROP] (F G : PROP → PROP) (hf : BIAntiProp F)
    (hg : BIAntiProp G) : BIAntiProp (λP : PROP => iprop(F P ∨ G P)) where
  anti_prop {P Q} := by
    iintro #H1 (HF | HG)
    · ileft
      iapply @hf.anti_prop P Q
      iexact H1
      iexact HF
    · iright
      iapply @hg.anti_prop P Q
      iexact H1
      iexact HG

-- TODO: antitone_imp

theorem antitone_forall [BI PROP] (F : A → PROP → PROP)
    (hf : ∀x, BIAntiProp (F x)) : BIAntiProp (λP : PROP => iprop(∀x, F x P)) where
  anti_prop {P Q} := by
    iintro #H1 H2 %a
    iapply @(hf a).anti_prop P
    · iexact H1
    · iexact H2

theorem antitone_exists [BI PROP] (F : A → PROP → PROP)
    (hf : ∀x, BIAntiProp (F x)) : BIAntiProp (λP : PROP => iprop(∃x, F x P)) where
  anti_prop {P Q} := by
    iintro #H1 ⟨%x, H2⟩
    iexists x
    iapply @(hf x).anti_prop P
    · iexact H1
    · iexact H2

theorem antitone_sep [BI PROP] (F G : PROP → PROP) (hf : BIAntiProp F)
    (hg : BIAntiProp G) : BIAntiProp (λP : PROP => iprop(F P ∗ G P)) where
  anti_prop {P Q} := by
    iintro #H1 ⟨HF, HG⟩
    isplitl [HF]
    · iapply @hf.anti_prop P Q
      · iexact H1
      · iexact HF
    · iapply @hg.anti_prop P Q
      · iexact H1
      · iexact HG

theorem antitone_wand [BI PROP] (F G : PROP → PROP) (hf : BIMonoProp F)
    (hg : BIAntiProp G) : BIAntiProp (λP : PROP => iprop(F P -∗ G P)) where
  anti_prop {P Q} := by
    iintro #H1 H2 HF
    iapply @hg.anti_prop P
    · iexact H1
    · iapply H2
      iapply @hf.mono_prop P Q
      · iexact H1
      · iexact HF

theorem antitone_persistently [BI PROP] (F : PROP → PROP) (hf : BIAntiProp F)
    : BIAntiProp (λP : PROP => iprop(<pers> F P)) where
  anti_prop {P Q} := by
    iintro #H1 #HF
    imodintro
    iapply @hf.anti_prop P Q
    · iexact H1
    · iexact HF

theorem antitone_later [BI PROP] (F : PROP → PROP) (hf : BIAntiProp F)
    : BIAntiProp (λP : PROP => iprop(▷ F P)) where
  anti_prop {P Q} := by
    iintro #H1 HP
    inext
    iapply @hf.anti_prop P Q
    · iexact H1
    · iexact HP

end antitone

section tactic

open Lean Meta Expr Elab Tactic Qq

private meta def solveUnary (goal : MVarId) (lem : Name) (PROP p : Expr)
    (pClass := ``BIMonoProp) : TacticM Unit := do
  let newF := Expr.lam .anonymous PROP p .default
  let mvarF ← mkFreshExprMVar (← mkAppM pClass #[newF])
  let proof ← mkAppM lem #[newF, mvarF]
  goal.assign proof
  replaceMainGoal [mvarF.mvarId!]

private meta def solveBinary (goal : MVarId) (lem : Name) (PROP p q : Expr)
    (pClass := ``BIMonoProp) (qClass := ``BIMonoProp): TacticM Unit := do
  let newF := Expr.lam .anonymous PROP p .default
  let newG := Expr.lam .anonymous PROP q .default
  let mvarF ← mkFreshExprMVar (← mkAppM pClass #[newF])
  let mvarG ← mkFreshExprMVar (← mkAppM qClass #[newG])
  let proof ← mkAppM lem #[newF, newG, mvarF, mvarG]
  goal.assign proof
  replaceMainGoal [mvarF.mvarId!, mvarG.mvarId!]

elab "monopropstep" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalDecl ← goal.getDecl
    let goalType := goalDecl.type

    if not goalType.isApp then throwError "isn't function application"

    goalType.withApp fun gFn gArgs => do
      if gFn.isConstOf ``BIMonoProp then
        let PROP := gArgs[0]!
        let BI := gArgs[1]!
        let f := gArgs[2]!
        let body := f.getLambdaBody

        if body.isApp then body.withApp fun fn args => do
          match fn.constName with
          | ``BI.and => solveBinary goal ``monotone_and PROP args[2]! args[3]!
          | ``BI.or => solveBinary goal ``monotone_or PROP args[2]! args[3]!
          | ``BI.sep => solveBinary goal ``monotone_sep PROP args[2]! args[3]!
          | ``BI.wand => solveBinary goal ``monotone_wand PROP args[2]! args[3]! (pClass := ``BIAntiProp)
          | ``BI.persistently => solveUnary goal ``monotone_persistently PROP args[2]!
          | ``BI.later => solveUnary goal ``monotone_later PROP args[2]!
          | _ => pure ()
        else if let .bvar 0 := body then
          let proof ← mkAppOptM ``monotone_id #[PROP, BI]
          goal.assign proof
        if not (body.hasLooseBVar 0) then
          let proof ← mkAppOptM ``monotone_const #[PROP, BI, body]
          goal.assign proof
      else if gFn.isConstOf ``BIAntiProp then
        let PROP := gArgs[0]!
        let BI := gArgs[1]!
        let f := gArgs[2]!
        let body := f.getLambdaBody

        if body.isApp then body.withApp fun fn args => do
          match fn.constName with
          | ``BI.and => solveBinary goal ``antitone_and PROP args[2]! args[3]! (pClass := ``BIAntiProp) (qClass := ``BIAntiProp)
          | ``BI.or => solveBinary goal ``antitone_or PROP args[2]! args[3]! (pClass := ``BIAntiProp) (qClass := ``BIAntiProp)
          | ``BI.sep => solveBinary goal ``antitone_sep PROP args[2]! args[3]! (pClass := ``BIAntiProp) (qClass := ``BIAntiProp)
          | ``BI.wand => solveBinary goal ``antitone_wand PROP args[2]! args[3]! (pClass := ``BIMonoProp) (qClass := ``BIAntiProp)
          | ``BI.persistently => solveUnary goal ``antitone_persistently PROP args[2]! (pClass := ``BIAntiProp)
          | ``BI.later => solveUnary goal ``antitone_later PROP args[2]! (pClass := ``BIAntiProp)
          | _ => pure ()
        if not (body.hasLooseBVar 0) then
          let proof ← mkAppOptM ``antitone_const #[PROP, BI, body]
          goal.assign proof
      else
        throwError "not BIMono"

macro "monoprop" : tactic =>
  `(tactic| repeat monopropstep)

example [BI PROP] : BIMonoProp (λP : PROP => iprop((▷ <pers> (P -∗ True)) -∗ P)) := by
  monoprop

end tactic
