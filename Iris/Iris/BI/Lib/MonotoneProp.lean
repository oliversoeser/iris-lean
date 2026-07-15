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

class BIMonoProp [BI PROP] (F : PROP → PROP) where
  mono_prop {P Q : PROP} : ⊢ □ (P -∗ Q) -∗ F P -∗ F Q

class BIAntiProp [BI PROP] (F : PROP → PROP) where
  anti_prop {P Q : PROP} : ⊢ □ (P -∗ Q) -∗ F Q -∗ F P

section monotone

instance monotone_const [BI PROP] (R : PROP) : BIMonoProp (λ_ => R) where
  mono_prop {P Q} := by
    iintro - HR
    iexact HR

instance monotone_id [BI PROP] : BIMonoProp (λR : PROP => R) where
  mono_prop {P Q} := by
    iintro #H
    iexact H

instance monotone_pure [BI PROP] (F : PROP → Prop)
    [hf : BIMonoProp (λP => iprop(⌜F P⌝ : PROP))] : BIMonoProp (λP : PROP => iprop(⌜F P⌝)) where
  mono_prop {P Q} := by
    iintro #H1 HP
    iapply @hf.mono_prop P Q
    · iexact H1
    · iexact HP

instance monotone_and [BI PROP] (F G : PROP → PROP) [hf : BIMonoProp F]
    [hg : BIMonoProp G] : BIMonoProp (λP : PROP => iprop(F P ∧ G P)) where
  mono_prop {P Q} := by
    iintro #H1 H2
    isplit
    · iapply @hf.mono_prop P Q
      · iexact H1
      · iexact H2
    · iapply @hg.mono_prop P Q
      · iexact H1
      · iexact H2

instance monotone_or [BI PROP] (F G : PROP → PROP) [hf : BIMonoProp F]
    [hg : BIMonoProp G] : BIMonoProp (λP : PROP => iprop(F P ∨ G P)) where
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

instance monotone_forall [BI PROP] (F : A → PROP → PROP)
    [hf : ∀x, BIMonoProp (F x)] : BIMonoProp (λP : PROP => iprop(∀x, F x P)) where
  mono_prop {P Q} := by
    iintro #H1 H2 %a
    iapply @(hf a).mono_prop P
    · iexact H1
    · iexact H2

instance monotone_exists [BI PROP] (F : A → PROP → PROP)
    [hf : ∀x, BIMonoProp (F x)] : BIMonoProp (λP : PROP => iprop(∃x, F x P)) where
  mono_prop {P Q} := by
    iintro #H1 ⟨%x, H2⟩
    iexists x
    iapply @(hf x).mono_prop P
    · iexact H1
    · iexact H2

instance monotone_sep [BI PROP] (F G : PROP → PROP) [hf : BIMonoProp F]
    [hg : BIMonoProp G] : BIMonoProp (λP : PROP => iprop(F P ∗ G P)) where
  mono_prop {P Q} := by
    iintro #H1 ⟨HF, HG⟩
    isplitl [HF]
    · iapply @hf.mono_prop P Q
      · iexact H1
      · iexact HF
    · iapply @hg.mono_prop P Q
      · iexact H1
      · iexact HG

instance monotone_wand [BI PROP] (F G : PROP → PROP) [hf : BIAntiProp F]
    [hg : BIMonoProp G] : BIMonoProp (λP : PROP => iprop(F P -∗ G P)) where
  mono_prop {P Q} := by
    iintro #H1 H2 HF
    iapply @hg.mono_prop P
    · iexact H1
    · iapply H2
      iapply @hf.anti_prop P Q
      · iexact H1
      · iexact HF

instance monotone_persistently [BI PROP] (F : PROP → PROP) [hf : BIMonoProp F]
    : BIMonoProp (λP : PROP => iprop(<pers> F P)) where
  mono_prop {P Q} := by
    iintro #H1 #HF
    imodintro
    iapply @hf.mono_prop P Q
    · iexact H1
    · iexact HF

instance monotone_later [BI PROP] (F : PROP → PROP) [hf : BIMonoProp F]
    : BIMonoProp (λP : PROP => iprop(▷ F P)) where
  mono_prop {P Q} := by
    iintro #H1 HP
    inext
    iapply @hf.mono_prop P Q
    · iexact H1
    · iexact HP

end monotone

section antitone

instance antitone_const [BI PROP] (R : PROP) : BIAntiProp (λ_ => R) where
  anti_prop {P Q} := by
    iintro - HR
    iexact HR

instance antitone_pure [BI PROP] (F : PROP → Prop)
    [hf : BIAntiProp (λP => iprop(⌜F P⌝ : PROP))] : BIAntiProp (λP : PROP => iprop(⌜F P⌝)) where
  anti_prop {P Q} := by
    iintro #H1 HP
    iapply @hf.anti_prop P Q
    · iexact H1
    · iexact HP

instance antitone_and [BI PROP] (F G : PROP → PROP) [hf : BIAntiProp F]
    [hg : BIAntiProp G] : BIAntiProp (λP : PROP => iprop(F P ∧ G P)) where
  anti_prop {P Q} := by
    iintro #H1 H2
    isplit
    · iapply @hf.anti_prop P Q
      · iexact H1
      · iexact H2
    · iapply @hg.anti_prop P Q
      · iexact H1
      · iexact H2

instance antitone_or [BI PROP] (F G : PROP → PROP) [hf : BIAntiProp F]
    [hg : BIAntiProp G] : BIAntiProp (λP : PROP => iprop(F P ∨ G P)) where
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

instance antitone_forall [BI PROP] (F : A → PROP → PROP)
    [hf : ∀x, BIAntiProp (F x)] : BIAntiProp (λP : PROP => iprop(∀x, F x P)) where
  anti_prop {P Q} := by
    iintro #H1 H2 %a
    iapply @(hf a).anti_prop P
    · iexact H1
    · iexact H2

instance antitone_exists [BI PROP] (F : A → PROP → PROP)
    [hf : ∀x, BIAntiProp (F x)] : BIAntiProp (λP : PROP => iprop(∃x, F x P)) where
  anti_prop {P Q} := by
    iintro #H1 ⟨%x, H2⟩
    iexists x
    iapply @(hf x).anti_prop P
    · iexact H1
    · iexact H2

instance antitone_sep [BI PROP] (F G : PROP → PROP) [hf : BIAntiProp F]
    [hg : BIAntiProp G] : BIAntiProp (λP : PROP => iprop(F P ∗ G P)) where
  anti_prop {P Q} := by
    iintro #H1 ⟨HF, HG⟩
    isplitl [HF]
    · iapply @hf.anti_prop P Q
      · iexact H1
      · iexact HF
    · iapply @hg.anti_prop P Q
      · iexact H1
      · iexact HG

instance antitone_wand [BI PROP] (F G : PROP → PROP) [hf : BIMonoProp F]
    [hg : BIAntiProp G] : BIAntiProp (λP : PROP => iprop(F P -∗ G P)) where
  anti_prop {P Q} := by
    iintro #H1 H2 HF
    iapply @hg.anti_prop P
    · iexact H1
    · iapply H2
      iapply @hf.mono_prop P Q
      · iexact H1
      · iexact HF

instance antitone_persistently [BI PROP] (F : PROP → PROP) [hf : BIAntiProp F]
    : BIAntiProp (λP : PROP => iprop(<pers> F P)) where
  anti_prop {P Q} := by
    iintro #H1 #HF
    imodintro
    iapply @hf.anti_prop P Q
    · iexact H1
    · iexact HF

instance antitone_later [BI PROP] (F : PROP → PROP) [hf : BIAntiProp F]
    : BIAntiProp (λP : PROP => iprop(▷ F P)) where
  anti_prop {P Q} := by
    iintro #H1 HP
    inext
    iapply @hf.anti_prop P Q
    · iexact H1
    · iexact HP

end antitone

section tactic

elab "monoprop" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalDecl ← goal.getDecl
    let goalType := goalDecl.type
    dbg_trace f!"goal type: {goalType}"

instance [BI PROP] : BIMonoProp (λP : PROP => P) := by
  monoprop
  sorry

end tactic
