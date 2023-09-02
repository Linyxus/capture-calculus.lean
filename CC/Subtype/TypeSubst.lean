import Mathlib.Data.Fin.Basic
import CC.Basic
import CC.Rename
import CC.CaptureSet
import CC.Type
import CC.Type.TypeSubst
import CC.Context
import CC.TypeMap
import CC.Subst
import CC.Typed
import CC.Typed.Basic
import CC.Subtype
import CC.Narrowing
import CC.Subcapt.TypeSubst
import CC.Narrowing

namespace CC

private def tsubst_motive (Γ : Ctx n m1) (S1 S2 : PType n m1) : Prop :=
  ∀ {m2} {f : TypeMap n m1 m2} {Δ : Ctx n m2},
    VarTypeMap Γ Δ f →
    TVarSubst Γ Δ f →
    SubtypeP Δ (S1.tsubst f) (S2.tsubst f)

private def tsubst_motive_ctype (Γ : Ctx n m1) (S1 S2 : CType n m1) : Prop :=
  ∀ {m2} {f : TypeMap n m1 m2} {Δ : Ctx n m2},
    VarTypeMap Γ Δ f →
    TVarSubst Γ Δ f →
    Subtype Δ (S1.tsubst f) (S2.tsubst f)

def SubtypeP.tsubst'
  (h : SubtypeP Γ S1 S2) :
  tsubst_motive Γ S1 S2 := by
  apply SubtypeP.rec
    (motive_1 := fun Γ T1 T2 _ => tsubst_motive_ctype Γ T1 T2)
    (motive_2 := fun Γ S1 S2 _ => tsubst_motive Γ S1 S2)
    <;> try (solve | trivial | aesop)
  case capt =>
    unfold tsubst_motive at *
    unfold tsubst_motive_ctype at *
    intros
    constructor <;> try trivial
    apply Subcapt.tsubst <;> trivial
    rename_i ih _ _ _ _ _
    apply ih <;> trivial
  case cap =>
    unfold tsubst_motive_ctype at *; intros; simp [CType.tsubst]; constructor
  case refl =>
    unfold tsubst_motive; intros
    apply SubtypeP.refl
  case trans =>
    unfold tsubst_motive; intros
    apply SubtypeP.trans <;> aesop
  case top =>
    unfold tsubst_motive; intros
    simp [PType.tsubst]
    apply SubtypeP.top
  case tvar =>
    unfold tsubst_motive; intros
    simp [PType.tsubst]
    rename_i δ
    apply δ; trivial
  case arr =>
    unfold tsubst_motive_ctype; unfold tsubst_motive; intros
    simp
    rename_i ih1 ih2 _ f Δ σ δ
    apply SubtypeP.arr
    apply ih1 <;> trivial
    apply ih2
    apply VarTypeMap.ext_var; trivial
    apply TVarSubst.ext_var; trivial
  case tarr =>
    unfold tsubst_motive_ctype; unfold tsubst_motive; intros
    simp
    rename_i ih1 ih2 _ f Δ σ δ
    apply SubtypeP.tarr
    apply ih1 <;> trivial
    apply ih2
    apply VarTypeMap.ext_tvar; trivial
    apply TVarSubst.ext_tvar; trivial
  case boxed =>
    unfold tsubst_motive_ctype; unfold tsubst_motive; intros
    simp
    rename_i ih _ f Δ σ δ
    apply SubtypeP.boxed
    apply ih <;> trivial

def SubtypeP.tsubst
  (h : SubtypeP Γ S1 S2)
  (σ : VarTypeMap Γ Δ g)
  (δ : TVarSubst Γ Δ g) :
  SubtypeP Δ (S1.tsubst g) (S2.tsubst g) := by
  apply SubtypeP.tsubst' <;> aesop

def Subtype.tsubst
  (h : Subtype Γ T1 T2)
  (σ : VarTypeMap Γ Δ g)
  (δ : TVarSubst Γ Δ g) :
  Subtype Δ (T1.tsubst g) (T2.tsubst g) := by
  cases h <;> try (solve | simp [CType.tsubst]; constructor)
  constructor
  apply Subcapt.tsubst <;> trivial
  apply SubtypeP.tsubst <;> trivial

def Subtype.narrow_tvar 
  (hsub : SubtypeP Γ T' T)
  (h0 : Subtype (Ctx.extend_tvar Γ T) T1 T2) :
  Subtype (Ctx.extend_tvar Γ T') T1 T2 := by
    rw [<- CType.tsubst_id (T := T1), <- CType.tsubst_id (T := T2)]
    apply Subtype.tsubst
    trivial
    apply VarTypeMap.narrowing_tvar
    apply TVarSubst.narrowing_tvar
    trivial
