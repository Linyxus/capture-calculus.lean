import Mathlib.Data.Fin.Basic
import CC.Basic
import CC.Rename
import CC.CaptureSet
import CC.Type
import CC.Type.TypeSubst
import CC.Context
import CC.TypeMap
import CC.Subst
import CC.Narrowing

namespace CC

def Subcapt.tsubst
  (h : Subcapt Γ C1 C2)
  (δ : VarTypeMap Γ Δ g) :
  Subcapt Δ C1 C2 := by
  induction h
  case sc_trans =>
    rename_i ih1 ih2
    apply Subcapt.sc_trans
    apply ih1; trivial
    apply ih2; trivial
  case sc_elem he =>
    apply Subcapt.sc_elem; trivial
  case sc_var hb =>
    apply Subcapt.sc_var
    have h1 := δ hb
    simp [CType.tsubst] at h1
    exact h1
  case sc_set ih ihr ihu =>
    apply Subcapt.sc_set
    · intros x he
      apply ih <;> trivial
    · intros x he
      apply ihr <;> trivial
    · intros hu
      apply ihu <;> trivial
  case sc_reach => apply Subcapt.sc_reach
  case sc_reach_cap => apply Subcapt.sc_reach_cap
  case sc_elem_reach => apply Subcapt.sc_elem_reach; trivial
  case sc_elem_cap => apply Subcapt.sc_elem_cap
