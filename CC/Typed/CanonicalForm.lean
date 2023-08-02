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
import CC.Typed.Inversion
import CC.Typed.Subst

namespace CC

theorem Typed.cf_fun' :
  t0 = Term.abs T' t ->
  T0 = CType.capt C (PType.arr T U) ->
  Typed Γ t0 Ct T0 ->
  ∃ C', Typed (Ctx.extend_var Γ T) t C' U := by
  intro he1 he2 h
  induction h <;> try (solve | cases he1 | cases he2)
  case abs h hd ih =>
    cases he1; cases he2
    aesop
  case sub h hsub ih =>
    cases he1; cases he2
    cases hsub; rename_i hc hs
    have h1 := SubtypeP.fun_inv hs
    cases h1
    case inl h1 =>
      cases h1; subst_vars
      exfalso
      apply Typed.value_typing <;> (solve | constructor | trivial)
    case inr h1 =>
      let ⟨T', U', he, hs1, hs2⟩ := h1
      clear h1
      subst_vars
      have ih' := ih rfl rfl
      cases ih'; rename_i C0 ih
      constructor
      apply Typed.sub
      apply Typed.narrow_var
      repeat trivial

theorem Typed.cf_fun :
  Typed Γ (Term.abs T' t) Ct (CType.capt C (PType.arr T U)) ->
  ∃ C', Typed (Ctx.extend_var Γ T) t C' U := by
  intro h
  apply Typed.cf_fun' <;> trivial
