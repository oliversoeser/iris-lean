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

instance monotone_constant [BI PROP] [OFE A] : BIMonoPred
    (λ_ : A → PROP => λ_ : A => P) where
  mono_pred {_ _ _ _} := by
    iintro _ %_ HP
    iexact HP
  mono_pred_ne := by infer_instance

instance monotone_id [BI PROP] [OFE A] : BIMonoPred
    (λΦ : A → PROP => Φ) where
  mono_pred {_ _ _ _} := by
    iintro #H
    iexact H
  mono_pred_ne := by infer_instance

instance monotone_persistently [BI PROP] [OFE A] (F : (A → PROP) → A → PROP) [hf : BIMonoPred F] :
    BIMonoPred (λΦ : A → PROP => λx : A => iprop(<pers> F Φ x)) where
  mono_pred {Φ Ψ h₁ h₂} := by
    iintro #H1 %x #H2
    imodintro
    iapply @hf.mono_pred Φ Ψ h₁ h₂
    iapply H1
    iexact H2
  mono_pred_ne {Φ h} := by
    constructor
    intro n x₁ x₂ hneq
    have h' := (@hf.mono_pred_ne Φ h).ne hneq
    exact persistently_ne.ne h'

instance monotone_later [BI PROP] [OFE A] (F : (A → PROP) → A → PROP) [hf : BIMonoPred F] :
    BIMonoPred (λΦ : A → PROP => λx : A => iprop(▷ F Φ x)) where
  mono_pred {Φ Ψ h₁ h₂} := by
    iintro #H1 %x H2
    inext
    iapply @hf.mono_pred Φ Ψ h₁ h₂
    iapply H1
    iexact H2
  mono_pred_ne {Φ h} := by
    constructor
    intro n x₁ x₂ hneq
    have h' := (@hf.mono_pred_ne Φ h).ne hneq
    exact later_ne.ne h'
