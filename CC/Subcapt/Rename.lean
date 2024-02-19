import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

import CC.Basic
import CC.Rename

import CC.CaptureSet
import CC.Context
import CC.Type
import CC.Subcapt

namespace CC

def Subcapt.rename (σ : VarRename Γ Δ f g) : Subcapt Γ C1 C2 -> Subcapt Δ (C1.rename f) (C2.rename f) := by
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
    apply Subcapt.sc_var
    have H := σ h
    simp at H
    assumption
  case sc_set hs hsr hsc =>
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
      have h := hsr x2 h2 σ
      rw [rename_singleton_reach] at h
      rw [<- eq2]
      assumption
    · intro hc; aesop
  case sc_reach => apply Subcapt.sc_reach
  case sc_elem_cap =>
    simp; simp [CaptureSet.rename]; apply Subcapt.sc_elem_cap
  case sc_elem_reach =>
    simp; simp [CaptureSet.rename]; apply Subcapt.sc_elem_reach
    simp; aesop
  case sc_reach_cap =>
    simp; apply Subcapt.sc_reach_cap
