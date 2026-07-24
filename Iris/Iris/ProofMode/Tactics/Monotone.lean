/-
Copyright (c) 2026 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
module

public import Iris.BI.Lib.Fixpoint
public import Iris.ProofMode.Classes

@[expose] public section

namespace Iris.ProofMode
open BI OFE

class MonotonePred [BI PROP] [OFE A] (F : (A → PROP) → (A → PROP)) where
  mono_pred {Φ Ψ : A → PROP} [NonExpansive Φ] [NonExpansive Ψ] :
    ⊢ □ (∀ x, Φ x -∗ Ψ x) -∗ ∀ x, F Φ x -∗ F Ψ x
  mono_pred_ne {Φ : A → PROP} [NonExpansive Φ] : NonExpansive (F Φ)
export MonotonePred (mono_pred mono_pred_ne)
attribute [instance] mono_pred_ne

class AntitonePred [BI PROP] [OFE A] (F : (A → PROP) → (A → PROP)) where
  anti_pred {Φ Ψ : A → PROP} [NonExpansive Φ] [NonExpansive Ψ] :
    ⊢ □ (∀ x, Φ x -∗ Ψ x) -∗ ∀ x, F Ψ x -∗ F Φ x
  anti_pred_ne {Φ : A → PROP} [NonExpansive Φ] : NonExpansive (F Φ)
export AntitonePred (anti_pred anti_pred_ne)
attribute [instance] anti_pred_ne

section monotone

instance monotone_const [BI PROP] [OFE A]
    [hne : NonExpansive Ω] : MonotonePred (λ_ : A → PROP => Ω) where
  mono_pred {Φ Ψ h₁ h₂} := by
    iintro #H1 %x H2
    iexact H2
  mono_pred_ne {Φ h} := by
    constructor
    intro n x₁ x₂ hneq
    exact hne.ne hneq

instance monotone_id [BI PROP] [OFE A] : MonotonePred (λΦ : A → PROP => Φ) where
  mono_pred {Φ Ψ h₁ h₂} := by
    iintro #H %x HΦ
    iapply H
    iexact HΦ
  mono_pred_ne {Φ h} := by
    constructor
    intro n x₁ x₂ hneq
    exact h.ne hneq

instance monotone_comp [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
    [hf : MonotonePred F] [hg : MonotonePred G] : MonotonePred (λΦ => F (G Φ)) where
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

instance monotone_and [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : MonotonePred F] [hg : MonotonePred G] :
    MonotonePred (λΦ : A → PROP => λx : A => iprop(F Φ x ∧ G Φ x)) where
  mono_pred {Φ Ψ h₁ h₂} := by
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

instance monotone_or [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : MonotonePred F] [hg : MonotonePred G] :
    MonotonePred (λΦ : A → PROP => λx : A => iprop(F Φ x ∨ G Φ x)) where
  mono_pred {Φ Ψ h₁ h₂} := by
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

instance monotone_pers_imp [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : AntitonePred F] [hg : MonotonePred G] :
    MonotonePred (λΦ : A → PROP => λx : A => iprop(<pers> F Φ x → G Φ x)) where
  mono_pred {Φ Ψ h₁ h₂} := by
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

instance monotone_sep [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : MonotonePred F] [hg : MonotonePred G] :
    MonotonePred (λΦ : A → PROP => λx : A => iprop(F Φ x ∗ G Φ x)) where
  mono_pred {Φ Ψ h₁ h₂} := by
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

instance monotone_wand [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : AntitonePred F] [hg : MonotonePred G] :
    MonotonePred (λΦ : A → PROP => λx : A => iprop(F Φ x -∗ G Φ x)) where
  mono_pred {Φ Ψ h₁ h₂} := by
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

instance monotone_persistently [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : MonotonePred F] : MonotonePred (λΦ : A → PROP => λx : A => iprop(<pers> F Φ x)) where
  mono_pred {Φ Ψ h₁ h₂} := by
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

instance monotone_later [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : MonotonePred F] : MonotonePred (λΦ : A → PROP => λx : A => iprop(▷ F Φ x)) where
  mono_pred {Φ Ψ h₁ h₂} := by
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

instance antitone_and [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : AntitonePred F] [hg : AntitonePred G] :
    AntitonePred (λΦ : A → PROP => λx : A => iprop(F Φ x ∧ G Φ x)) where
  anti_pred {Φ Ψ h₁ h₂} := by
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

instance antitone_or [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : AntitonePred F] [hg : AntitonePred G] :
    AntitonePred (λΦ : A → PROP => λx : A => iprop(F Φ x ∨ G Φ x)) where
  anti_pred {Φ Ψ h₁ h₂} := by
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

instance antitone_pers_imp [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : MonotonePred F] [hg : AntitonePred G] :
    AntitonePred (λΦ : A → PROP => λx : A => iprop(<pers> F Φ x → G Φ x)) where
  anti_pred {Φ Ψ h₁ h₂} := by
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

instance antitone_sep [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : AntitonePred F] [hg : AntitonePred G] :
    AntitonePred (λΦ : A → PROP => λx : A => iprop(F Φ x ∗ G Φ x)) where
  anti_pred {Φ Ψ h₁ h₂} := by
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

instance antitone_wand [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : MonotonePred F] [hg : AntitonePred G] :
    AntitonePred (λΦ : A → PROP => λx : A => iprop(F Φ x -∗ G Φ x)) where
  anti_pred {Φ Ψ h₁ h₂} := by
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

instance antitone_persistently [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : AntitonePred F] : AntitonePred (λΦ : A → PROP => λx : A => iprop(<pers> F Φ x)) where
  anti_pred {Φ Ψ h₁ h₂} := by
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

instance antitone_later [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : AntitonePred F] : AntitonePred (λΦ : A → PROP => λx : A => iprop(▷ F Φ x)) where
  anti_pred {Φ Ψ h₁ h₂} := by
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
