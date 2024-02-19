import Mathlib.Data.Fin.Basic
import CC.Basic
import CC.Rename
import CC.CaptureSet
import CC.Type
import CC.Type.TypeSubst
import CC.Term.TypeSubst
import CC.Context
import CC.TypeMap
import CC.Subst
import CC.Typed
import CC.Typed.Basic
import CC.Subtype
import CC.Narrowing
import CC.Subtype.TypeSubst

namespace CC

theorem RefinePType.tsubst (h : RefinePType S x v S') :
  RefinePType (S.tsubst g) x v (S'.tsubst g) := by
  rename_i n m1 m2
  induction h generalizing m2
    <;> try (solve | simp [PType.tsubst]; constructor)
  case arr ih => simp [PType.tsubst]; constructor; trivial; aesop
  case tarr ih => simp [PType.tsubst]; constructor; trivial; aesop
  case boxed ih => simp [PType.tsubst]; constructor; trivial; aesop

def Typed.tsubst {Δ : Ctx n m2}
  (h : Typed Γ t C T)
  (σ : VarTypeMap Γ Δ g)
  (δ : TVarSubst Γ Δ g) :
  Typed Δ (t.tsubst g) C (T.tsubst g) := by
  induction h generalizing m2
  case var hb =>
    simp [Term.tsubst, CType.tsubst]
    have hb' := σ hb
    simp [CType.tsubst] at hb'
    constructor; trivial
  case var_refine hr ih =>
    apply Typed.var_refine
    apply ih <;> trivial
    apply RefinePType.tsubst; trivial
  case sub ih =>
    apply Typed.sub
    apply ih <;> trivial
    apply Subtype.tsubst <;> trivial
  case abs ih =>
    simp [Term.tsubst]
    apply Typed.abs
    apply ih
    apply VarTypeMap.ext_var; trivial
    apply TVarSubst.ext_var; trivial
    trivial
  case tabs ih =>
    simp [Term.tsubst]
    apply Typed.tabs
    apply ih
    apply VarTypeMap.ext_tvar; trivial
    apply TVarSubst.ext_tvar; trivial
  case app ih1 ih2 =>
    simp [Term.tsubst]
    rw [CType.tsubst_open_var_comm]
    simp [Term.tsubst] at ih1 ih2
    apply Typed.app
    apply ih1 <;> trivial
    apply ih2 <;> trivial
    trivial
  case tapp ih =>
    simp [Term.tsubst]
    rw [CType.tsubst_open_tvar_comm]
    simp [Term.tsubst] at ih
    apply Typed.tapp
    apply ih <;> trivial
  case box ih =>
    simp [Term.tsubst] at *
    apply Typed.box
    apply ih <;> trivial
  case unbox ih =>
    simp [Term.tsubst] at *
    apply Typed.unbox
    apply ih <;> trivial
  case letval1 ih1 ih2 =>
    simp [Term.tsubst] at *
    apply Typed.letval1
    apply ih1 <;> trivial
    apply ih2 <;> try trivial
    apply VarTypeMap.ext_var; trivial
    apply TVarSubst.ext_var; trivial
    subst_vars
    simp [CType.tsubst_weaken_var_comm]
    trivial
  case letval2 ih1 ih2 =>
    simp [Term.tsubst] at *
    apply Typed.letval2
    apply ih1 <;> trivial
    apply Value.tsubst; trivial
    apply ih2
    apply VarTypeMap.ext_var; trivial
    apply TVarSubst.ext_var; trivial
    subst_vars
    simp [CType.tsubst_weaken_var_comm]
    trivial

def Typed.narrow_tvar
  (hsub : SubtypeP Γ T2 T1)
  (h0 : Typed (Ctx.extend_tvar Γ T1) t Ct T) :
  Typed (Ctx.extend_tvar Γ T2) t Ct T := by
  rw [<- Term.tsubst_id (t := t), <- CType.tsubst_id (T := T)]
  apply Typed.tsubst <;> try trivial
  apply VarTypeMap.narrowing_tvar
  apply TVarSubst.narrowing_tvar
  trivial
