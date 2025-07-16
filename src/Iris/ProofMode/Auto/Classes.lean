/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.BI

namespace Iris.ProofMode.Auto
open Iris.BI

class Refl [BI PROP] (P : PROP) where
  refl : P ⊢ P
export Refl (refl)

class FromAnd [BI PROP] (P Q R : PROP) where
  from_and : P ∧ Q ⊢ R
export FromAnd (from_and)
