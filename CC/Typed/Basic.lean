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

namespace CC

theorem Typed.var_inv_subcapt' : 
  t0 = Term.var x ->
  T0 = CType.capt C S ->
  Typed Γ t0 Cx T0 ->
  Subcapt Γ {x} C := by
  intro eq1 eq2 h
  induction h 
  case var =>
    cases eq1
    cases eq2
    apply Subcapt.refl
  case sub ih =>
    rename_i T T' _ _
    cases T
    have ih := ih eq1 rfl
    rename_i hsub _
    cases hsub
    rename_i hsub _
    cases eq2
    apply Subcapt.sc_trans
    exact ih
    aesop
  all_goals cases eq1

theorem Typed.var_inv_subcapt :
  Typed Γ (Term.var x) Cx (CType.capt C S) ->
  Subcapt Γ {x} C := by
  apply Typed.var_inv_subcapt' <;> aesop

theorem Typed.app_inv' :
  t0 = Term.app x y ->
  Typed Γ t0 C0 U ->
  ∃ Cx Cy Cf T U0, Typed Γ (Term.var x) Cx (CType.capt Cf (PType.arr T U0)) ∧ 
    Typed Γ (Term.var y) Cy T ∧
    Subtype Γ (U0.open_var y) U := by
  intro heq h
  induction h <;> try (solve | cases heq)
  case app h1 h2 _ _ =>
    cases heq
    repeat (apply Exists.intro)
    apply And.intro
    exact h1
    apply And.intro
    exact h2
    apply Subtype.refl
  case sub h hsub ih =>
    have ih' := ih heq
    let ⟨Cx0, Cy0, Cf0, T0, U0, hx, hy, heq0⟩ := ih'
    clear ih
    subst_vars
    repeat apply Exists.intro
    apply And.intro
    exact hx
    apply And.intro
    exact hy
    apply Subtype.trans <;> aesop

theorem Typed.app_inv :
  Typed Γ (Term.app x y) C0 U ->
  ∃ Cx Cy Cf T U0, Typed Γ (Term.var x) Cx (CType.capt Cf (PType.arr T U0)) ∧ 
    Typed Γ (Term.var y) Cy T ∧
    Subtype Γ (U0.open_var y) U := by
  apply Typed.app_inv'
  rfl

theorem Typed.var_typing_bound' :
  t0 = Term.var x ->
  T0 = CType.capt C S ->
  Typed Γ t0 Cx T0 ->
  ∃ C' S', BoundVar Γ x (CType.capt C' S') ∧ SubtypeP Γ S' S := by
  intro he1 he2 h
  induction h <;> try (solve | cases he1 | cases he2)
  case var hb =>
    cases he1; cases he2
    repeat (apply Exists.intro)
    apply And.intro
    exact hb
    apply SubtypeP.refl
  case sub T _ h hsub ih =>
    cases he1; cases he2
    cases T
    have ih := ih rfl rfl
    let ⟨C', S, hb, hsub0⟩ := ih
    repeat (apply Exists.intro)
    apply And.intro
    exact hb
    cases hsub
    apply SubtypeP.trans <;> trivial

theorem Typed.var_typing_bound :
  Typed Γ (Term.var x) Cx (CType.capt C S) ->
  ∃ C' S', BoundVar Γ x (CType.capt C' S') ∧ SubtypeP Γ S' S := by 
  apply Typed.var_typing_bound' <;> aesop

theorem Typed.var_typing_captures'
  (he : t0 = Term.var x)
  (h : Typed Γ t0 Cx T) :
  Cx = {x} := by
  induction h <;> try (solve | cases he | aesop)

theorem Typed.var_typing_captures
  (h : Typed Γ (Term.var x) Cx T) :
  Cx = {x} := by
  apply Typed.var_typing_captures' <;> trivial
