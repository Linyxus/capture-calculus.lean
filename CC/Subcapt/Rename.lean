import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

import CC.Basic
import CC.Rename

import CC.CaptureSet
import CC.Context
import CC.Type
import CC.Subcapt

namespace CC

def IsReader.rename (h : IsReader Γ S) (δ : TVarRename Γ Δ f g) :
  IsReader Δ (S.rename f g) := by
  induction h
  case reader => simp [PType.rename]; constructor
  case widen ih =>
    simp [PType.rename]; constructor
    aesop
    assumption

def Subcapt.rename (σ : VarRename Γ Δ f g) (δ : TVarRename Γ Δ f g) : Subcapt Γ C1 C2 -> Subcapt Δ (C1.rename f) (C2.rename f) := by
  intro h
  induction h
  case sc_trans ih1 ih2 =>
    apply Subcapt.sc_trans
    apply ih1 <;> aesop
    apply ih2 <;> aesop
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
  case sc_set hs hr1 hr2 =>
    apply Subcapt.sc_set
    intro x1 h1
    rw [mem_rename] at h1
    let ⟨x2, ⟨h2, eq2⟩⟩ := h1
    have h := hs x2 h2 σ δ
    rw [rename_singleton] at h
    rw [<- eq2]
    assumption
    apply hr1 <;> assumption
    apply hr2 <;> assumption
  case sc_elem_rdr => simp [CaptureSet.rename]; apply Subcapt.sc_elem_rdr
  case sc_elem_cap => simp [CaptureSet.rename]; apply Subcapt.sc_elem_cap
  case sc_rdr_cap => simp [CaptureSet.rename]; apply Subcapt.sc_rdr_cap
  case sc_reader hb hr =>
    rw [rename_singleton]
    simp [CaptureSet.rename]
    apply Subcapt.sc_reader
    have hb' := σ hb
    exact hb'
    apply IsReader.rename <;> trivial
