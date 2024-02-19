import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

import CC.Basic
import CC.Rename

import CC.CaptureSet
import CC.Context
import CC.Type
import CC.Subcapt
import CC.Subcapt.Basic
import CC.Subcapt.Rename
import CC.Subtype

namespace CC

theorem Subtype.refl :
  Subtype Γ T T := by
  cases T
  case capt =>
    constructor
    apply Subcapt.refl
    apply SubtypeP.refl
  case cap => 
    constructor
    apply Subcapt.refl

theorem Subtype.trans
  (h1 : Subtype Γ T1 T2)
  (h2 : Subtype Γ T2 T3) :
  Subtype Γ T1 T3 := by
  cases h1
  case capt =>
    cases h2
    case capt =>
      constructor
      apply Subcapt.sc_trans <;> trivial
      apply SubtypeP.trans <;> trivial
  case cap => 
    cases h2; constructor
    apply Subcapt.sc_trans <;> trivial
