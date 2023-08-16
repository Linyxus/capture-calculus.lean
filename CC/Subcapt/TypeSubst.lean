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
  case sc_set ih ihr1 ihr2 =>
    apply Subcapt.sc_set
    intros x he
    apply ih <;> trivial; aesop; aesop
  case sc_elem_rdr => apply sc_elem_rdr
  case sc_elem_cap => apply sc_elem_cap
  case sc_rdr_cap => apply sc_rdr_cap
