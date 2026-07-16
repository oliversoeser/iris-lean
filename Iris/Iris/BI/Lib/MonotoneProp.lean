/-
Copyright (c) 2026 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
module

public import Iris.BI.Lib.Fixpoint
public import Mathlib.Tactic.FunProp

@[expose] public section

namespace Iris
open BI OFE

@[fun_prop]
class BIMonoProp [BI PROP] (F : PROP → PROP) where
  mono_prop {P Q : PROP} : ⊢ □ (P -∗ Q) -∗ F P -∗ F Q

@[fun_prop]
class BIAntiProp [BI PROP] (F : PROP → PROP) where
  anti_prop {P Q : PROP} : ⊢ □ (P -∗ Q) -∗ F Q -∗ F P

section monotone

@[fun_prop]
instance monotone_const [BI PROP] (R : PROP) : BIMonoProp (λ_ => R) where
  mono_prop {P Q} := by
    iintro - HR
    iexact HR

@[fun_prop]
instance monotone_id [BI PROP] : BIMonoProp (λR : PROP => R) where
  mono_prop {P Q} := by
    iintro #H
    iexact H

@[fun_prop]
instance monotone_comp [BI PROP] (F G : PROP → PROP) [hf : BIMonoProp F]
    [hg : BIMonoProp G] : BIMonoProp (λP : PROP => F (G P)) where
  mono_prop {P Q} := by
    iintro #H
    iapply @hf.mono_prop (G P)
    imodintro
    iapply @hg.mono_prop
    iexact H

-- TODO: monotone_prop

@[fun_prop]
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

@[fun_prop]
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

@[fun_prop]
instance monotone_forall [BI PROP] (F : A → PROP → PROP)
    [hf : ∀x, BIMonoProp (F x)] : BIMonoProp (λP : PROP => iprop(∀x, F x P)) where
  mono_prop {P Q} := by
    iintro #H1 H2 %a
    iapply @(hf a).mono_prop P
    · iexact H1
    · iexact H2

@[fun_prop]
instance monotone_exists [BI PROP] (F : A → PROP → PROP)
    [hf : ∀x, BIMonoProp (F x)] : BIMonoProp (λP : PROP => iprop(∃x, F x P)) where
  mono_prop {P Q} := by
    iintro #H1 ⟨%x, H2⟩
    iexists x
    iapply @(hf x).mono_prop P
    · iexact H1
    · iexact H2

@[fun_prop]
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

@[fun_prop]
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

@[fun_prop]
theorem monotone_persistently [BI PROP] (F : PROP → PROP) [hf : BIMonoProp F]
    : BIMonoProp (λP : PROP => iprop(<pers> F P)) where
  mono_prop {P Q} := by
    iintro #H1 #HF
    imodintro
    iapply @hf.mono_prop P Q
    · iexact H1
    · iexact HF

@[fun_prop]
theorem monotone_later [BI PROP] (F : PROP → PROP) [hf : BIMonoProp F]
    : BIMonoProp (λP : PROP => iprop(▷ F P)) where
  mono_prop {P Q} := by
    iintro #H1 HP
    inext
    iapply @hf.mono_prop P Q
    · iexact H1
    · iexact HP

end monotone

section antitone

@[fun_prop]
instance antitone_const [BI PROP] (R : PROP) : BIAntiProp (λ_ => R) where
  anti_prop {P Q} := by
    iintro - HR
    iexact HR

@[fun_prop]
instance antitone_comp₁ [BI PROP] (F G : PROP → PROP) [hf : BIAntiProp F]
    [hg : BIMonoProp G] : BIAntiProp (λP : PROP => F (G P)) where
  anti_prop {P Q} := by
    iintro #H
    iapply @hf.anti_prop (G P)
    imodintro
    iapply @hg.mono_prop
    iexact H

@[fun_prop]
instance antitone_comp₂ [BI PROP] (F G : PROP → PROP) [hf : BIMonoProp F]
    [hg : BIAntiProp G] : BIAntiProp (λP : PROP => F (G P)) where
  anti_prop {P Q} := by
    iintro #H
    iapply @hf.mono_prop (G Q)
    imodintro
    iapply @hg.anti_prop
    iexact H

-- TODO: antitone_prop

@[fun_prop]
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

@[fun_prop]
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

@[fun_prop]
instance antitone_forall [BI PROP] (F : A → PROP → PROP)
    [hf : ∀x, BIAntiProp (F x)] : BIAntiProp (λP : PROP => iprop(∀x, F x P)) where
  anti_prop {P Q} := by
    iintro #H1 H2 %a
    iapply @(hf a).anti_prop P
    · iexact H1
    · iexact H2

@[fun_prop]
instance antitone_exists [BI PROP] (F : A → PROP → PROP)
    [hf : ∀x, BIAntiProp (F x)] : BIAntiProp (λP : PROP => iprop(∃x, F x P)) where
  anti_prop {P Q} := by
    iintro #H1 ⟨%x, H2⟩
    iexists x
    iapply @(hf x).anti_prop P
    · iexact H1
    · iexact H2

@[fun_prop]
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

@[fun_prop]
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

@[fun_prop]
instance antitone_persistently [BI PROP] (F : PROP → PROP) [hf : BIAntiProp F]
    : BIAntiProp (λP : PROP => iprop(<pers> F P)) where
  anti_prop {P Q} := by
    iintro #H1 #HF
    imodintro
    iapply @hf.anti_prop P Q
    · iexact H1
    · iexact HF

@[fun_prop]
instance antitone_later [BI PROP] (F : PROP → PROP) [hf : BIAntiProp F]
    : BIAntiProp (λP : PROP => iprop(▷ F P)) where
  anti_prop {P Q} := by
    iintro #H1 HP
    inext
    iapply @hf.anti_prop P Q
    · iexact H1
    · iexact HP

end antitone
