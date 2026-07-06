/-
Copyright (c) 2026 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
module

public import Iris.BI.Classes
public import Iris.BI.Extensions
public import Iris.BI.BI
public import Iris.BI.DerivedLaws
public import Iris.Std.Nat
public import Iris.Std.Classes
public import Iris.Std.Rewrite
public import Iris.Std.TC
import Iris.Std.RocqPorting

@[expose] public section

namespace Iris.BI
open Iris.Std BI

instance entails_ccpo [BI PROP] [OFE.Leibniz PROP] : Lean.Order.CCPO PROP where
  rel := Entails
  rel_refl := .rfl
  rel_trans := .trans
  rel_antisymm h1 h2 := BIBase.BiEntails.to_eq <| entails_antisymm.antisymm h1 h2
  has_csup {c} _ := by
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
