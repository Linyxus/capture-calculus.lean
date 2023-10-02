import Mathlib.Data.Fin.Basic
import CC.Basic
import CC.CaptureSet
import CC.Type
import CC.Context
import CC.TypeMap
import CC.Subst
import CC.Typed
import CC.Typed.Basic
import CC.Subcapt

namespace CC

def Subcapt.subst (σ : VarSubst Γ Δ f) :
  Subcapt Γ C1 C2 ->
  Subcapt Δ (C1.rename f) (C2.rename f) := by
  intro h
  induction h
  case sc_trans ih1 ih2 =>
    apply Subcapt.sc_trans
    apply ih1; aesop
    apply ih2; aesop
  case sc_elem h =>
    simp
    apply Subcapt.sc_elem
    apply mem_rename_of_mem; assumption
  case sc_var h =>
    simp
    have h' := σ h
    simp [CType.rename] at h'
    apply Typed.var_inv_subcapt; aesop
  case sc_set hs =>
    apply Subcapt.sc_set
    intro x1 h1
    rw [mem_rename] at h1
    let ⟨x2, ⟨h2, eq2⟩⟩ := h1
    have h := hs x2 h2 σ
    rw [rename_singleton] at h
    rw [<- eq2]
    assumption
  case sc_nest h =>
    simp [rename_singleton]
    have h' := σ h
    simp [CType.rename] at h'
    apply Typed.var_inv_subcapt_cap; trivial
