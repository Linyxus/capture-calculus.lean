import Mathlib.Data.Fin.Basic
import CC.Basic
import CC.Rename
import CC.CaptureSet
import CC.Type
import CC.Context
import CC.TypeMap
import CC.Subst
import CC.Typed
import CC.Typed.Basic
import CC.Typed.Rename
import CC.Subtype
import CC.Subtype.Subst

namespace CC

theorem Typed.precise_var' (h : Typed Γ t Cx T) :
  t = Term.var x ->
  T = CType.capt C S ->
  Typed Γ t Cx (CType.capt {x} S) := by
  intro heq1 heq2
  induction h <;> try (solve | cases heq1 | cases heq2)
  case var =>
    rename_i T0 _; cases T0 <;> try (solve | cases heq2)
    cases heq1; cases heq2
    rw [<- CType.at_capt]
    constructor
    trivial
  case sub =>
    rename_i hsub ih
    subst_vars
    rename_i T0 _
    cases T0
    case capt =>
      have ih' := ih rfl rfl
      apply Typed.sub
      apply ih'
      constructor
      apply Subcapt.refl
      cases hsub; assumption
    case cap => cases hsub

lemma Typed.precise_var_cap'
  (he1 : t0 = Term.var x)
  (he2 : T0 = CType.cap o)
  (h : Typed Γ t0 Cx T0) :
  Typed Γ (Term.var x) Cx (CType.cap x) := by
  induction h <;> try (solve | cases he1 | cases he2)
  case var hb =>
    cases he1
    rename_i T0; cases T0 <;> cases he2
    rw [<- CType.at_cap]
    constructor; trivial
  case sub hx hsub ih =>
    cases he1; cases he2
    cases hsub
    have ih' := ih rfl rfl
    assumption

lemma Typed.precise_var_cap
  (h : Typed Γ (Term.var x) Cx (CType.cap o)) :
  Typed Γ (Term.var x) Cx (CType.cap x) :=
  Typed.precise_var_cap' rfl rfl h

def Typed.subst {Γ : Ctx n1 m} (h : Typed Γ t C T)
  {Δ : Ctx n2 m}
  (σ : VarSubst Γ Δ f) (δ : TVarRename Γ Δ f id) :
  Typed Δ (t.rename f id) (C.rename f) (T.rename f id) := by
  induction h generalizing n2
  case var T0 hb =>
    have h' := σ hb
    cases T0 <;> simp [Term.rename] at *
    case capt =>
      apply Typed.precise_var' <;> try rfl
      exact h'
    case cap => 
      apply Typed.precise_var_cap
      simp [CType.at, CType.rename] at *; trivial
  case sub hsub ih => 
    apply Typed.sub
    apply ih <;> trivial
    apply Subtype.subst hsub <;> aesop
  case abs ih =>
    simp [Term.rename]
    apply Typed.abs
    apply ih
    apply VarSubst.ext_var; trivial
    apply TVarRename.ext_var; trivial
    apply DropBinder.rename; trivial
  case tabs ih =>
    simp [Term.rename]
    apply Typed.tabs
    apply ih
    apply VarSubst.ext_tvar; trivial
    rw [<- id_ext]
    apply TVarRename.ext_tvar; trivial
  case app ih1 ih2 =>
    simp [Term.rename]
    simp [CType.rename_open_comm, CaptureSet.rename_union]
    have ih1' := ih1 σ δ
    have ih2' := ih2 σ δ
    apply Typed.app
    simp [Term.rename] at ih1' ih2'
    apply ih1'
    apply ih2'
  case tapp ih =>
    simp [Term.rename]
    simp [CType.rename_open_tvar_comm]
    have ih' := ih σ δ
    apply Typed.tapp
    simp [Term.rename] at ih'
    apply ih'
  case box ih =>
    simp [Term.rename]
    simp [CType.rename_open_comm, CaptureSet.rename_union]
    have ih' := ih σ δ
    apply Typed.box
    simp [Term.rename] at ih'
    apply ih'
  case unbox ih =>
    simp [Term.rename]
    simp [CType.rename_open_comm, CaptureSet.rename_union]
    have ih' := ih σ δ
    apply Typed.unbox
    simp [Term.rename] at ih'
    apply ih'
  case letval1 ih1 ih2 => 
    simp [Term.rename]
    simp [CaptureSet.rename_union]
    apply Typed.letval1
    apply ih1 <;> trivial
    apply ih2
    apply VarSubst.ext_var; trivial
    apply TVarRename.ext_var; trivial
    subst_vars
    simp [CType.rename_weaken_comm]
    apply DropBinder.rename; trivial
  case letval2 ih1 ih2 =>
    simp [Term.rename]
    simp [CaptureSet.rename_union]
    apply Typed.letval2
    apply ih1 <;> trivial
    apply Value.rename; trivial
    apply ih2
    apply VarSubst.ext_var; trivial
    apply TVarRename.ext_var; trivial
    subst_vars
    simp [CType.rename_weaken_comm]
    apply DropBinderFree.rename; trivial

def Typed.narrow_var
  (hsub : Subtype Γ T1 T2)
  (h0 : Typed (Ctx.extend_var Γ T2) t Ct T) :
  Typed (Ctx.extend_var Γ T1) t Ct T := by
  have h := Typed.subst h0 (VarSubst.narrowing_var hsub) TVarRename.narrowing_var
  rw [<- Term.rename_id (t := t), <- CaptureSet.rename_id (C := Ct), <- CType.rename_id (T := T)]
  assumption

def Typed.open_var
  (hz : Typed Γ (Term.var z) {z} P)
  (h0 : Typed (Ctx.extend_var Γ P) t C T) :
  Typed Γ (t.open_var z) (C.open_var z) (T.open_var z) := by
  apply Typed.subst <;> try trivial
  apply VarSubst.open_var; trivial
  apply TVarRename.open_var; trivial
