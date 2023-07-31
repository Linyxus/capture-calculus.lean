import Mathlib.Data.Fin.Basic
import CC.Basic
import CC.CaptureSet
import CC.Type
import CC.Context
import CC.TypeMap
import CC.Typed
import CC.Subcapt
import CC.Subcapt.Basic

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