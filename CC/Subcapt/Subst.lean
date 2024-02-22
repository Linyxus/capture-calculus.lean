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
    apply Typed.var_inv_subcapt
    have h'' := h'.left
    trivial
  case sc_region hb =>
    simp
    have h' := σ hb
    have h'' := h'.right
    simp [Region.rename] at h''; cases h''
    trivial
  case sc_set hs hr hu =>
    apply Subcapt.sc_set
    · intro x1 h1
      rw [mem_rename] at h1
      let ⟨x2, ⟨h2, eq2⟩⟩ := h1
      have h := hs x2 h2 σ
      rw [rename_singleton] at h
      rw [<- eq2]
      assumption
    · intro x1 h1
      rw [mem_reach_rename] at h1
      let ⟨x2, ⟨h2, eq2⟩⟩ := h1
      have h := hr x2 h2 σ
      rw [rename_singleton_reach] at h
      rw [<- eq2]
      assumption
    · intro hc; aesop
  case sc_reach => simp; apply Subcapt.sc_reach
  case sc_elem_cap => simp; simp [CaptureSet.rename]; apply Subcapt.sc_elem_cap
  case sc_elem_reach =>
    simp; apply Subcapt.sc_elem_reach
    apply mem_rename_of_mem_reach; assumption
  case sc_reach_cap => simp; apply Subcapt.sc_reach_cap
