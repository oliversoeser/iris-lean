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

abbrev Arr := (· → ·)

@[fun_prop]
class BIMonoPred' [BI PROP] [OFE A] (F : (A → PROP) → (A → PROP)) where
  mono_pred {Φ Ψ : A → PROP} [NonExpansive Φ] [NonExpansive Ψ] :
    ⊢ □ (∀ x, Φ x -∗ Ψ x) -∗ ∀ x, F Φ x -∗ F Ψ x
  mono_pred_ne {Φ : A → PROP} [NonExpansive Φ] : NonExpansive (F Φ)
export BIMonoPred' (mono_pred mono_pred_ne)
attribute [instance] BIMonoPred'.mono_pred_ne

theorem mono_pred' [BI PROP] [OFE A] {F : (A → PROP) → (A → PROP)} (hf : BIMonoPred' F) : BIMonoPred F where
  mono_pred := hf.mono_pred
  mono_pred_ne := hf.mono_pred_ne

@[fun_prop]
class BIAntiPred [BI PROP] [OFE A] (F : (A → PROP) → (A → PROP)) where
  anti_pred {Φ Ψ : A → PROP} [NonExpansive Φ] [NonExpansive Ψ] :
    ⊢ □ (∀ x, Φ x -∗ Ψ x) -∗ ∀ x, F Ψ x -∗ F Φ x
  anti_pred_ne {Φ : A → PROP} [NonExpansive Φ] : NonExpansive (F Φ)
export BIAntiPred (anti_pred anti_pred_ne)
attribute [instance] anti_pred_ne

section monotone

@[fun_prop]
instance monotone_const [BI PROP] [OFE A]
    [hne : NonExpansive Ξ] : BIMonoPred' (λ_ : A → PROP => Ξ) where
  mono_pred {Φ Ψ h₁ h₂} := by
    iintro #H1 %x H2
    iexact H2
  mono_pred_ne {Φ h} := by
    constructor
    intro n x₁ x₂ hneq
    exact hne.ne hneq

@[fun_prop]
instance monotone_id [BI PROP] [OFE A] : BIMonoPred' (λΦ : Arr A PROP => Φ) where
  mono_pred {Φ Ψ h₁ h₂} := by
    iintro #H %x HΦ
    iapply H
    iexact HΦ
  mono_pred_ne {Φ h} := by
    constructor
    intro n x₁ x₂ hneq
    exact h.ne hneq

@[fun_prop]
instance monotone_comp [BI PROP] [OFE A] (F G : (Arr A PROP) → Arr A PROP)
    [hf : BIMonoPred' F] [hg : BIMonoPred' G] : BIMonoPred' (λΦ => F (G Φ)) where
  mono_pred {Φ Ψ h₁ h₂} := by
    iintro #H %x HΦ
    iapply @hf.mono_pred (G Φ)
    · imodintro
      iapply @hg.mono_pred
      iexact H
    · iexact HΦ
  mono_pred_ne {Φ h} := by
    constructor
    intro n x₁ x₂ hneq
    apply @hf.mono_pred_ne.ne
    exact hneq

def And [BIBase PROP] (F G : Arr A PROP) (x : A) := iprop(F x ∧ G x)

@[fun_prop]
instance monotone_and [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : BIMonoPred' F] [hg : BIMonoPred' G] :
    BIMonoPred' (λΦ : A → PROP => (And (F Φ) (G Φ))) where
  mono_pred {Φ Ψ h₁ h₂} := by
    unfold And
    iintro #H1 %x H2
    isplit
    · iapply @hf.mono_pred Φ Ψ h₁ h₂
      iexact H1
      iexact H2
    · iapply @hg.mono_pred Φ Ψ h₁ h₂
      iexact H1
      iexact H2
  mono_pred_ne {Φ h} := by
    constructor
    intro n x₁ x₂ hneq
    have h₁ := (@hf.mono_pred_ne Φ h).ne hneq
    have h₂ := (@hg.mono_pred_ne Φ h).ne hneq
    exact and_ne.ne h₁ h₂

def Or [BIBase PROP] (F G : Arr A PROP) (x : A) := iprop(F x ∨ G x)

@[fun_prop]
instance monotone_or [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : BIMonoPred' F] [hg : BIMonoPred' G] :
    BIMonoPred' (λΦ : A → PROP => Or (F Φ) (G Φ)) where
  mono_pred {Φ Ψ h₁ h₂} := by
    unfold Or
    iintro #H %x (HF | HG)
    · ileft
      iapply @hf.mono_pred Φ Ψ h₁ h₂
      iexact H
      iexact HF
    · iright
      iapply @hg.mono_pred Φ Ψ h₁ h₂
      iexact H
      iexact HG
  mono_pred_ne {Φ h} := by
    constructor
    intro n x₁ x₂ hneq
    have h₁ := (@hf.mono_pred_ne Φ h).ne hneq
    have h₂ := (@hg.mono_pred_ne Φ h).ne hneq
    exact or_ne.ne h₁ h₂

def PersImp [BIBase PROP] (F G : Arr A PROP) (x : A) := iprop(<pers> F x → G x)

@[fun_prop]
instance monotone_pers_imp [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : BIAntiPred F] [hg : BIMonoPred' G] :
    BIMonoPred' (λΦ : A → PROP => PersImp (F Φ) (G Φ)) where
  mono_pred {Φ Ψ h₁ h₂} := by
    unfold PersImp
    iintro #H1 %x H2 #HF
    iapply @hg.mono_pred Φ Ψ h₁ h₂
    · iexact H1
    · iapply (@intuitionistically_wand _ _ (F Φ x)).mpr $$ [H2]
      iexact H2
      imodintro
      iapply @hf.anti_pred Φ Ψ h₁ h₂
      · iexact H1
      · iexact HF
  mono_pred_ne {Φ h} := by
    constructor
    intro n x₁ x₂ hneq
    have h₁ := persistently_ne.ne ((@hf.anti_pred_ne Φ h).ne hneq)
    have h₂ := (@hg.mono_pred_ne Φ h).ne hneq
    exact imp_ne.ne h₁ h₂

def Sep [BIBase PROP] (F G : Arr A PROP) (x : A) := iprop(F x ∗ G x)

@[fun_prop]
instance monotone_sep [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : BIMonoPred' F] [hg : BIMonoPred' G] :
    BIMonoPred' (λΦ : A → PROP => Sep (F Φ) (G Φ)) where
  mono_pred {Φ Ψ h₁ h₂} := by
    unfold Sep
    iintro #H %x ⟨HF, HG⟩
    isplitl [HF]
    · iapply @hf.mono_pred Φ Ψ h₁ h₂
      iexact H
      iexact HF
    · iapply @hg.mono_pred Φ Ψ h₁ h₂
      iexact H
      iexact HG
  mono_pred_ne {Φ h} := by
    constructor
    intro n x₁ x₂ hneq
    have h₁ := (@hf.mono_pred_ne Φ h).ne hneq
    have h₂ := (@hg.mono_pred_ne Φ h).ne hneq
    exact sep_ne.ne h₁ h₂

def Wand [BIBase PROP] (F G : Arr A PROP) (x : A) := iprop(F x -∗ G x)

@[fun_prop]
instance monotone_wand [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : BIAntiPred F] [hg : BIMonoPred' G] :
    BIMonoPred' (λΦ : A → PROP => Wand (F Φ) (G Φ)) where
  mono_pred {Φ Ψ h₁ h₂} := by
    unfold Wand
    iintro #H1 %x H2 HF
    iapply @hg.mono_pred Φ Ψ h₁ h₂
    · iexact H1
    · iapply H2
      iapply @hf.anti_pred Φ Ψ h₁ h₂
      · iexact H1
      · iexact HF
  mono_pred_ne {Φ h} := by
    constructor
    intro n x₁ x₂ hneq
    have h₁ := (@hf.anti_pred_ne Φ h).ne hneq
    have h₂ := (@hg.mono_pred_ne Φ h).ne hneq
    exact wand_ne.ne h₁ h₂

def Persistently [BIBase PROP] (F : Arr A PROP) (x : A) := iprop(<pers> F x)

@[fun_prop]
instance monotone_persistently [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : BIMonoPred' F] : BIMonoPred' (λΦ : A → PROP => Persistently (F Φ)) where
  mono_pred {Φ Ψ h₁ h₂} := by
    unfold Persistently
    iintro #H1 %x #H2
    imodintro
    iapply @hf.mono_pred Φ Ψ h₁ h₂
    iexact H1
    iexact H2
  mono_pred_ne {Φ h} := by
    constructor
    intro n x₁ x₂ hneq
    have h' := (@hf.mono_pred_ne Φ h).ne hneq
    exact persistently_ne.ne h'

def Lat [BIBase PROP] (F : Arr A PROP) (x : A) := iprop(▷ F x)

@[fun_prop]
instance monotone_later [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : BIMonoPred' F] : BIMonoPred' (λΦ : A → PROP => Lat (F Φ)) where
  mono_pred {Φ Ψ h₁ h₂} := by
    unfold Lat
    iintro #H1 %x H2
    inext
    iapply @hf.mono_pred Φ Ψ h₁ h₂
    iexact H1
    iexact H2
  mono_pred_ne {Φ h} := by
    constructor
    intro n x₁ x₂ hneq
    have h' := (@hf.mono_pred_ne Φ h).ne hneq
    exact later_ne.ne h'

end monotone

section antitone

@[fun_prop]
instance antitone_and [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : BIAntiPred F] [hg : BIAntiPred G] :
    BIAntiPred (λΦ : A → PROP => And (F Φ) (G Φ)) where
  anti_pred {Φ Ψ h₁ h₂} := by
    unfold And
    iintro #H1 %x H2
    isplit
    · iapply @hf.anti_pred Φ Ψ h₁ h₂
      iexact H1
      iexact H2
    · iapply @hg.anti_pred Φ Ψ h₁ h₂
      iexact H1
      iexact H2
  anti_pred_ne {Φ h} := by
    constructor
    intro n x₁ x₂ hneq
    have h₁ := (@hf.anti_pred_ne Φ h).ne hneq
    have h₂ := (@hg.anti_pred_ne Φ h).ne hneq
    exact and_ne.ne h₁ h₂

@[fun_prop]
instance antitone_or [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : BIAntiPred F] [hg : BIAntiPred G] :
    BIAntiPred (λΦ : A → PROP => Or (F Φ) (G Φ)) where
  anti_pred {Φ Ψ h₁ h₂} := by
    unfold Or
    iintro #H %x (HF | HG)
    · ileft
      iapply @hf.anti_pred Φ Ψ h₁ h₂
      iexact H
      iexact HF
    · iright
      iapply @hg.anti_pred Φ Ψ h₁ h₂
      iexact H
      iexact HG
  anti_pred_ne {Φ h} := by
    constructor
    intro n x₁ x₂ hneq
    have h₁ := (@hf.anti_pred_ne Φ h).ne hneq
    have h₂ := (@hg.anti_pred_ne Φ h).ne hneq
    exact or_ne.ne h₁ h₂

@[fun_prop]
instance antitone_pers_imp [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : BIMonoPred' F] [hg : BIAntiPred G] :
    BIAntiPred (λΦ : A → PROP => PersImp (F Φ) (G Φ)) where
  anti_pred {Φ Ψ h₁ h₂} := by
    unfold PersImp
    iintro #H1 %x H2 #HF
    iapply @hg.anti_pred Φ Ψ h₁ h₂
    · iexact H1
    · iapply (@intuitionistically_wand _ _ (F Ψ x)).mpr $$ [H2]
      iexact H2
      imodintro
      iapply @hf.mono_pred Φ Ψ h₁ h₂
      · iexact H1
      · iexact HF
  anti_pred_ne {Φ h} := by
    constructor
    intro n x₁ x₂ hneq
    have h₁ := persistently_ne.ne ((@hf.mono_pred_ne Φ h).ne hneq)
    have h₂ := (@hg.anti_pred_ne Φ h).ne hneq
    exact imp_ne.ne h₁ h₂

@[fun_prop]
instance antitone_sep [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : BIAntiPred F] [hg : BIAntiPred G] :
    BIAntiPred (λΦ : A → PROP => Sep (F Φ) (G Φ)) where
  anti_pred {Φ Ψ h₁ h₂} := by
    unfold Sep
    iintro #H %x ⟨HF, HG⟩
    isplitl [HF]
    · iapply @hf.anti_pred Φ Ψ h₁ h₂
      iexact H
      iexact HF
    · iapply @hg.anti_pred Φ Ψ h₁ h₂
      iexact H
      iexact HG
  anti_pred_ne {Φ h} := by
    constructor
    intro n x₁ x₂ hneq
    have h₁ := (@hf.anti_pred_ne Φ h).ne hneq
    have h₂ := (@hg.anti_pred_ne Φ h).ne hneq
    exact sep_ne.ne h₁ h₂

@[fun_prop]
instance antitone_wand [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : BIMonoPred' F] [hg : BIAntiPred G] :
    BIAntiPred (λΦ : A → PROP => Wand (F Φ) (G Φ)) where
  anti_pred {Φ Ψ h₁ h₂} := by
    unfold Wand
    iintro #H1 %x H2 HF
    iapply @hg.anti_pred Φ Ψ h₁ h₂
    · iexact H1
    · iapply H2
      iapply @hf.mono_pred Φ Ψ h₁ h₂
      · iexact H1
      · iexact HF
  anti_pred_ne {Φ h} := by
    constructor
    intro n x₁ x₂ hneq
    have h₁ := (@hf.mono_pred_ne Φ h).ne hneq
    have h₂ := (@hg.anti_pred_ne Φ h).ne hneq
    exact wand_ne.ne h₁ h₂

@[fun_prop]
instance antitone_persistently [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : BIAntiPred F] : BIAntiPred (λΦ : A → PROP => Persistently (F Φ)) where
  anti_pred {Φ Ψ h₁ h₂} := by
    unfold Persistently
    iintro #H1 %x #H2
    imodintro
    iapply @hf.anti_pred Φ Ψ h₁ h₂
    iexact H1
    iexact H2
  anti_pred_ne {Φ h} := by
    constructor
    intro n x₁ x₂ hneq
    have h' := (@hf.anti_pred_ne Φ h).ne hneq
    exact persistently_ne.ne h'

@[fun_prop]
instance antitone_later [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : BIAntiPred F] : BIAntiPred (λΦ : A → PROP => Lat (F Φ)) where
  anti_pred {Φ Ψ h₁ h₂} := by
    unfold Lat
    iintro #H1 %x H2
    inext
    iapply @hf.anti_pred Φ Ψ h₁ h₂
    iexact H1
    iexact H2
  anti_pred_ne {Φ h} := by
    constructor
    intro n x₁ x₂ hneq
    have h' := (@hf.anti_pred_ne Φ h).ne hneq
    exact later_ne.ne h'

end antitone
