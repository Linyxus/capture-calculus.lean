import Mathlib.Data.Fin.Basic

import CC.Basic
import CC.CaptureSet
import CC.Type
import CC.Context
import CC.TypeMap
import CC.Typed
import CC.Subcapt
import CC.Subcapt.Basic
import CC.Subtype.Basic
import CC.Subtype.Inversion

namespace CC

theorem Typed.value_typing
  (h : Typed Γ t C T)
  (hval : Value t) :
  T ≠ CType.capt C0 (PType.tvar X) := by
  induction h <;> try (solve | cases hval | aesop)
  case sub =>
    rename_i ht hsub ih
    intro he
    subst_vars
    cases hsub; rename_i hsub
    have h1 := SubtypeP.tvar_inv hsub
    cases h1
    subst_vars
    aesop

theorem Typed.val_inv_fun'
  (hv : Value t)
  (he : T0 = CType.capt C (PType.arr D T U))
  (h : Typed Γ t Ct T0) : 
  ∃ u1 u2, t = Term.abs D u1 u2 := by
  induction h <;> try (solve | cases he | cases hv)
  case sub ht hsub ih => 
    subst_vars
    cases hsub; rename_i hsub
    have h0 := SubtypeP.fun_inv hsub
    cases h0 with
    | inl h0 =>
      cases h0; subst_vars
      exfalso; apply Typed.value_typing
      exact ht
      exact hv
      rfl
    | inr h0 =>
      let ⟨T0, U0, he, _⟩ := h0
      subst_vars
      aesop
  case abs => aesop

theorem Typed.val_inv_fun
  (hv : Value t)
  (h : Typed Γ t Ct (CType.capt C (PType.arr D T U))) : 
  ∃ u1 u2, t = Term.abs D u1 u2 := by apply Typed.val_inv_fun' <;> trivial

theorem Typed.val_inv_tfun'
  (hv : Value t)
  (he : T0 = CType.capt C (PType.tarr T U))
  (h : Typed Γ t Ct T0) : 
  ∃ S u, t = Term.tabs S u := by
  induction h <;> try (solve | cases he | cases hv | aesop)
  case sub ht hsub ih => 
    subst_vars
    cases hsub; rename_i hsub
    have h0 := SubtypeP.tfun_inv hsub
    cases h0 with
    | inl h0 =>
      cases h0; subst_vars
      exfalso; apply Typed.value_typing
      exact ht
      exact hv
      rfl
    | inr h0 =>
      let ⟨T0, U0, he, _⟩ := h0
      subst_vars
      aesop

theorem Typed.val_inv_tfun
  (hv : Value t)
  (h : Typed Γ t Ct (CType.capt C (PType.tarr T U))) : 
  ∃ S u, t = Term.tabs S u := by apply Typed.val_inv_tfun' <;> trivial

theorem Typed.val_inv_box'
  (hv : Value t)
  (he : T0 = CType.capt C (PType.boxed T))
  (h : Typed Γ t Ct T0) : 
  ∃ x, t = Term.box x := by
  induction h <;> try (solve | cases he | cases hv | aesop)
  case sub ht hsub ih =>
    subst_vars
    cases hsub; rename_i hsub
    have h0 := SubtypeP.boxed_inv hsub
    cases h0 with
    | inl h0 =>
      cases h0; subst_vars
      exfalso; apply Typed.value_typing
      exact ht
      exact hv
      rfl
    | inr h0 =>
      let ⟨T0, he, _⟩ := h0
      subst_vars
      aesop

theorem Typed.val_inv_box
  (hv : Value t)
  (h : Typed Γ t Ct (CType.capt C (PType.boxed T))) : 
  ∃ x, t = Term.box x := by apply Typed.val_inv_box' <;> trivial
