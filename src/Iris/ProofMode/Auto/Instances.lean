/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.BI
import Iris.ProofMode.Auto.Classes
import Iris.Std.TC

namespace Iris.ProofMode.Auto
open Iris.BI Iris.Std

instance fromAnd_and [BI PROP] (P1 P2 : PROP) :
    FromAnd P1 P2 iprop(P1 ∧ P2) := ⟨.rfl⟩
