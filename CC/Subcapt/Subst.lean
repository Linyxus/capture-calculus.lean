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

def IsReader.subst 
  (h : IsReader Γ S)
  (σ : VarSubst Γ Δ f) (δ : TVarRename Γ Δ f id) :
  IsReader Δ (S.rename f id) := by
  induction h
  case reader => simp [PType.rename]; apply reader
  case widen hb hr ih =>
    simp [PType.rename]
    apply widen
    apply δ; assumption
    trivial

def Subcapt.subst (σ : VarSubst Γ Δ f) (δ : TVarRename Γ Δ f id) :
  Subcapt Γ C1 C2 ->
  Subcapt Δ (C1.rename f) (C2.rename f) := by
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
    have h' := σ h
    simp [CType.rename] at h'
    apply Typed.var_inv_subcapt; aesop
  case sc_set hs hr1 hr2 =>
    apply Subcapt.sc_set
    intro x1 h1
    rw [mem_rename] at h1
    let ⟨x2, ⟨h2, eq2⟩⟩ := h1
    have h := hs x2 h2 σ δ
    rw [rename_singleton] at h
    rw [<- eq2]
    assumption
    aesop; aesop
  case sc_elem_rdr => apply sc_elem_rdr
  case sc_elem_cap => apply sc_elem_cap
  case sc_rdr_cap => apply sc_rdr_cap
  case sc_reader hb hr =>
    simp; simp [CaptureSet.rename]
    have hb' := σ hb
    simp at hb'
    have h0 := Typed.var_typing_bound hb'
    have ⟨D, C', S', hb'', hsub⟩ := h0
    apply sc_reader
    exact hb''
    apply IsReader.subtype_pres; exact hsub
    apply hr.subst <;> trivial
