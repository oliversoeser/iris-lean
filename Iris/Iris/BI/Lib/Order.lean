/-
Copyright (c) 2026 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
module

public import Iris.BI.DerivedLaws

@[expose] public section

namespace Iris
open BI Lean.Order

section entailment_order

abbrev EntailmentOrder (PROP : Type u) [BI PROP] := PROP

instance EntailmentOrder.instOrder [BI PROP] [OFE.Leibniz PROP] : PartialOrder (EntailmentOrder PROP) where
  rel x y := Entails x y
  rel_refl := .rfl
  rel_trans := .trans
  rel_antisymm h1 h2 := BIBase.BiEntails.to_eq <| entails_antisymm.antisymm h1 h2

instance EntailmentOrder.instCompleteLattice [BI PROP] [OFE.Leibniz PROP] : CompleteLattice PROP where
  has_sup {c} := by
    exists sExists (λP => c P)
    intro x
    constructor
    case mp =>
      intro h y cy
      refine BIBase.Entails.trans ?_ h
      exact sExists_intro cy
    case mpr =>
      intro h
      exact sExists_elim h

instance EntailmentOrder.instCCPO [BI PROP] [OFE.Leibniz PROP] : CCPO PROP where
  has_csup {c} _ := EntailmentOrder.instCompleteLattice.has_sup c

@[partial_fixpoint_monotone] theorem entailment_order_monotone_pure
    [BI PROP] [OFE.Leibniz PROP] {α} [PartialOrder α] (f : α → Prop)
    (h : @monotone _ _ _ ImplicationOrder.instOrder f) :
    @monotone _ _ _ (@EntailmentOrder.instOrder PROP _ _) (fun x => iprop(⌜f x⌝)) :=
  fun x y hxy => pure_mono (h x y hxy)

@[partial_fixpoint_monotone] theorem entailment_order_monotone_and
    [BI PROP] [OFE.Leibniz PROP] {α} [PartialOrder α]
    (f₁ : α → PROP) (f₂ : α → PROP)
    (h₁ : @monotone _ _ _ EntailmentOrder.instOrder f₁)
    (h₂ : @monotone _ _ _ EntailmentOrder.instOrder f₂) :
    @monotone _ _ _ EntailmentOrder.instOrder (fun x => iprop(f₁ x ∧ f₂ x)) :=
  fun x y hxy => and_mono (h₁ x y hxy) (h₂ x y hxy)

@[partial_fixpoint_monotone] theorem entailment_order_monotone_or
    [BI PROP] [OFE.Leibniz PROP] {α} [PartialOrder α]
    (f₁ : α → PROP) (f₂ : α → PROP)
    (h₁ : @monotone _ _ _ EntailmentOrder.instOrder f₁)
    (h₂ : @monotone _ _ _ EntailmentOrder.instOrder f₂) :
    @monotone _ _ _ EntailmentOrder.instOrder (fun x => iprop(f₁ x ∨ f₂ x)) :=
  fun x y hxy => or_mono (h₁ x y hxy) (h₂ x y hxy)

@[partial_fixpoint_monotone] theorem entailment_order_monotone_forall
    [BI PROP] [OFE.Leibniz PROP] {α} [PartialOrder α] {β} (f : α → β → PROP)
    (h : monotone f) :
    @monotone _ _ _ EntailmentOrder.instOrder (fun x => iprop(∀ y, f x y)) :=
  fun x y hxy => forall_mono (h x y hxy)

@[partial_fixpoint_monotone] theorem entailment_order_monotone_exists
    [BI PROP] [OFE.Leibniz PROP] {α} [PartialOrder α] {β} (f : α → β → PROP)
    (h : monotone f) :
    @monotone _ _ _ EntailmentOrder.instOrder (fun x => iprop(∃ y, f x y)) :=
  fun x y hxy => exists_mono (h x y hxy)

@[partial_fixpoint_monotone] theorem entailment_order_monotone_sep
    [BI PROP] [OFE.Leibniz PROP] {α} [PartialOrder α]
    (f₁ : α → PROP) (f₂ : α → PROP)
    (h₁ : @monotone _ _ _ EntailmentOrder.instOrder f₁)
    (h₂ : @monotone _ _ _ EntailmentOrder.instOrder f₂) :
    @monotone _ _ _ EntailmentOrder.instOrder (fun x => iprop(f₁ x ∗ f₂ x)) :=
  fun x y hxy => sep_mono (h₁ x y hxy) (h₂ x y hxy)

@[partial_fixpoint_monotone] theorem entailment_order_monotone_persistently
    [BI PROP] [OFE.Leibniz PROP] {α} [PartialOrder α] (f : α → PROP)
    (h : @monotone _ _ _ EntailmentOrder.instOrder f) :
    @monotone _ _ _ EntailmentOrder.instOrder (fun x => iprop(<pers> f x)) :=
  fun x y hxy => persistently_mono (h x y hxy)

@[partial_fixpoint_monotone] theorem entailment_order_monotone_later
    [BI PROP] [OFE.Leibniz PROP] {α} [PartialOrder α] (f : α → PROP)
    (h : @monotone _ _ _ EntailmentOrder.instOrder f) :
    @monotone _ _ _ EntailmentOrder.instOrder (fun x => iprop(▷ f x)) :=
  fun x y hxy => later_mono (h x y hxy)

end entailment_order

section reverse_entailment_order

abbrev ReverseEntailmentOrder (PROP : Type u) [BI PROP] := PROP

instance ReverseEntailmentOrder.instOrder [BI PROP] [OFE.Leibniz PROP] : PartialOrder PROP where
  rel x y := Entails y x
  rel_refl := .rfl
  rel_trans h1 h2 := .trans h2 h1
  rel_antisymm h1 h2 := BIBase.BiEntails.to_eq <| entails_antisymm.antisymm h2 h1

instance ReverseEntailmentOrder.instCompleteLattice [BI PROP] [OFE.Leibniz PROP] : CompleteLattice PROP where
  has_sup {c} := by
    exists sForall (λP => c P)
    intro x
    constructor
    case mp =>
      intro h y cy
      apply BIBase.Entails.trans h
      exact sForall_elim cy
    case mpr =>
      intro h
      exact sForall_intro h

instance ReverseEntailmentOrder.instCCPO [BI PROP] [OFE.Leibniz PROP] : CCPO PROP where
  has_csup {c} _ := ReverseEntailmentOrder.instCompleteLattice.has_sup c

@[partial_fixpoint_monotone] theorem reverse_entailment_order_monotone_pure
    [BI PROP] [OFE.Leibniz PROP] {α} [PartialOrder α] (f : α → Prop)
    (h : @monotone _ _ _ ReverseImplicationOrder.instOrder f) :
    @monotone _ _ _ (@ReverseEntailmentOrder.instOrder PROP _ _) (fun x => iprop(⌜f x⌝)) :=
  fun x y hxy => pure_mono (h x y hxy)

@[partial_fixpoint_monotone] theorem reverse_entailment_order_monotone_and
    [BI PROP] [OFE.Leibniz PROP] {α} [PartialOrder α]
    (f₁ : α → PROP) (f₂ : α → PROP)
    (h₁ : @monotone _ _ _ ReverseEntailmentOrder.instOrder f₁)
    (h₂ : @monotone _ _ _ ReverseEntailmentOrder.instOrder f₂) :
    @monotone _ _ _ ReverseEntailmentOrder.instOrder (fun x => iprop(f₁ x ∧ f₂ x)) :=
  fun x y hxy => and_mono (h₁ x y hxy) (h₂ x y hxy)

@[partial_fixpoint_monotone] theorem reverse_entailment_order_monotone_or
    [BI PROP] [OFE.Leibniz PROP] {α} [PartialOrder α]
    (f₁ : α → PROP) (f₂ : α → PROP)
    (h₁ : @monotone _ _ _ ReverseEntailmentOrder.instOrder f₁)
    (h₂ : @monotone _ _ _ ReverseEntailmentOrder.instOrder f₂) :
    @monotone _ _ _ ReverseEntailmentOrder.instOrder (fun x => iprop(f₁ x ∨ f₂ x)) :=
  fun x y hxy => or_mono (h₁ x y hxy) (h₂ x y hxy)

@[partial_fixpoint_monotone] theorem reverse_entailment_order_monotone_forall
    [BI PROP] [OFE.Leibniz PROP] {α} [PartialOrder α] {β} (f : α → β → PROP)
    (h : monotone f) :
    @monotone _ _ _ ReverseEntailmentOrder.instOrder (fun x => iprop(∀ y, f x y)) :=
  fun x y hxy => forall_mono (h x y hxy)

@[partial_fixpoint_monotone] theorem reverse_entailment_order_monotone_exists
    [BI PROP] [OFE.Leibniz PROP] {α} [PartialOrder α] {β} (f : α → β → PROP)
    (h : monotone f) :
    @monotone _ _ _ ReverseEntailmentOrder.instOrder (fun x => iprop(∃ y, f x y)) :=
  fun x y hxy => exists_mono (h x y hxy)

@[partial_fixpoint_monotone] theorem reverse_entailment_order_monotone_sep
    [BI PROP] [OFE.Leibniz PROP] {α} [PartialOrder α]
    (f₁ : α → PROP) (f₂ : α → PROP)
    (h₁ : @monotone _ _ _ ReverseEntailmentOrder.instOrder f₁)
    (h₂ : @monotone _ _ _ ReverseEntailmentOrder.instOrder f₂) :
    @monotone _ _ _ ReverseEntailmentOrder.instOrder (fun x => iprop(f₁ x ∗ f₂ x)) :=
  fun x y hxy => sep_mono (h₁ x y hxy) (h₂ x y hxy)

@[partial_fixpoint_monotone] theorem reverse_entailment_order_monotone_persistently
    [BI PROP] [OFE.Leibniz PROP] {α} [PartialOrder α] (f : α → PROP)
    (h : @monotone _ _ _ ReverseEntailmentOrder.instOrder f) :
    @monotone _ _ _ ReverseEntailmentOrder.instOrder (fun x => iprop(<pers> f x)) :=
  fun x y hxy => persistently_mono (h x y hxy)

@[partial_fixpoint_monotone] theorem reverse_entailment_order_monotone_later
    [BI PROP] [OFE.Leibniz PROP] {α} [PartialOrder α] (f : α → PROP)
    (h : @monotone _ _ _ ReverseEntailmentOrder.instOrder f) :
    @monotone _ _ _ ReverseEntailmentOrder.instOrder (fun x => iprop(▷ f x)) :=
  fun x y hxy => later_mono (h x y hxy)

end reverse_entailment_order

section antitone

@[partial_fixpoint_monotone] theorem entailment_order_monotone_imp
    [BI PROP] [OFE.Leibniz PROP] {α} [PartialOrder α] (f₁ : α → PROP)
    (f₂ : α → PROP)
    (h₁ : @monotone _ _ _ ReverseEntailmentOrder.instOrder f₁)
    (h₂ : @monotone _ _ _ EntailmentOrder.instOrder f₂):
    @monotone _ _ _ EntailmentOrder.instOrder (fun x => iprop(f₁ x → f₂ x)) :=
  fun x y hxy => imp_mono (h₁ x y hxy) (h₂ x y hxy)

@[partial_fixpoint_monotone] theorem reverse_entailment_order_monotone_imp
    [BI PROP] [OFE.Leibniz PROP] {α} [PartialOrder α] (f₁ : α → PROP)
    (f₂ : α → PROP)
    (h₁ : @monotone _ _ _ EntailmentOrder.instOrder f₁)
    (h₂ : @monotone _ _ _ ReverseEntailmentOrder.instOrder f₂):
    @monotone _ _ _ ReverseEntailmentOrder.instOrder (fun x => iprop(f₁ x → f₂ x)) :=
  fun x y hxy => imp_mono (h₁ x y hxy) (h₂ x y hxy)

@[partial_fixpoint_monotone] theorem entailment_order_monotone_wand
    [BI PROP] [OFE.Leibniz PROP] {α} [PartialOrder α] (f₁ : α → PROP)
    (f₂ : α → PROP)
    (h₁ : @monotone _ _ _ ReverseEntailmentOrder.instOrder f₁)
    (h₂ : @monotone _ _ _ EntailmentOrder.instOrder f₂):
    @monotone _ _ _ EntailmentOrder.instOrder (fun x => iprop(f₁ x -∗ f₂ x)) :=
  fun x y hxy => wand_mono (h₁ x y hxy) (h₂ x y hxy)

@[partial_fixpoint_monotone] theorem reverse_entailment_order_monotone_wand
    [BI PROP] [OFE.Leibniz PROP] {α} [PartialOrder α] (f₁ : α → PROP)
    (f₂ : α → PROP)
    (h₁ : @monotone _ _ _ EntailmentOrder.instOrder f₁)
    (h₂ : @monotone _ _ _ ReverseEntailmentOrder.instOrder f₂):
    @monotone _ _ _ ReverseEntailmentOrder.instOrder (fun x => iprop(f₁ x -∗ f₂ x)) :=
  fun x y hxy => wand_mono (h₁ x y hxy) (h₂ x y hxy)

end antitone
