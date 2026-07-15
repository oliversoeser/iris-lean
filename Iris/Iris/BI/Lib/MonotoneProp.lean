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
