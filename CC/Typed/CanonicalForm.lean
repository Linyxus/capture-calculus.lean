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
import CC.Typed.TypeSubst

namespace CC

theorem Typed.cf_fun' :
  t0 = Term.abs T' t ->
  T0 = CType.capt C (PType.arr T U) ->
  Typed Γ t0 Ct T0 ->
  ∃ C', Typed (Ctx.extend_var Γ T Region.glob) t C' U := by
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
  ∃ C', Typed (Ctx.extend_var Γ T Region.glob) t C' U := by
  intro h
  apply Typed.cf_fun' <;> trivial

theorem Typed.cf_tfun' :
  t0 = Term.tabs T' t ->
  T0 = CType.capt C (PType.tarr T U) ->
  Typed Γ t0 Ct T0 ->
  ∃ C', Typed (Ctx.extend_tvar Γ T) t C' U := by
  intro he1 he2 h
  induction h <;> try (solve | cases he1 | cases he2)
  case tabs h ih =>
    cases he1; cases he2
    aesop
  case sub h hsub ih =>
    cases he1; cases he2
    cases hsub; rename_i hc hs
    have h1 := SubtypeP.tfun_inv hs
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
      apply Typed.narrow_tvar
      repeat trivial

theorem Typed.cf_tfun :
  Typed Γ (Term.tabs T' t) Ct (CType.capt C (PType.tarr T U)) ->
  ∃ C', Typed (Ctx.extend_tvar Γ T) t C' U := by
  intro h
  apply Typed.cf_tfun' <;> trivial

theorem Typed.cf_box' :
  t0 = Term.box y ->
  T0 = CType.capt C (PType.boxed T) ->
  Typed Γ t0 Ct T0 ->
  ∃ C', Typed Γ (Term.var y) C' T := by
  intro he1 he2 h
  induction h <;> try (solve | cases he1 | cases he2)
  case box h ih =>
    cases he1; cases he2
    aesop
  case sub h hsub ih =>
    cases he1; cases he2
    cases hsub; rename_i hc hs
    have h1 := SubtypeP.boxed_inv hs
    cases h1
    case inl h1 =>
      cases h1; subst_vars
      exfalso
      apply Typed.value_typing <;> (solve | constructor | trivial)
    case inr h1 =>
      let ⟨T', he, hs⟩ := h1
      clear h1
      subst_vars
      have ih' := ih rfl rfl
      cases ih'; rename_i C0 ih
      constructor
      apply Typed.sub <;> trivial

theorem Typed.cf_box :
  Typed Γ (Term.box y) Ct (CType.capt C (PType.boxed T)) ->
  ∃ C', Typed Γ (Term.var y) C' T := by
  intro h
  apply Typed.cf_box' <;> trivial
