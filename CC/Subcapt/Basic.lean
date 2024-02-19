import Mathlib.Data.Fin.Basic
import CC.Basic
import CC.CaptureSet
import CC.Type
import CC.Context
import CC.TypeMap
import CC.Subst
import CC.Typed
import CC.Subcapt

namespace CC

def Subcapt.refl :
  Subcapt Γ C C := by
  apply Subcapt.sc_set
  · intro x0 h
    apply Subcapt.sc_elem
    aesop
  · intro x0 h
    apply Subcapt.sc_elem_reach
    aesop
  · intro h
    unfold CaptureSet.isUniversal at h
    cases C; cases h
    apply Subcapt.sc_elem_cap
