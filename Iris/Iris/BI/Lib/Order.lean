/-
Copyright (c) 2026 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
module

public import Iris.BI.DerivedLaws

@[expose] public section

namespace Iris
open Iris.Std BI Lean.Order

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
