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
import CC.Subtype
import CC.Subcapt.Subst
import CC.Narrowing

namespace CC

def SubtypeP.subst (σ : VarSubst Γ Δ f) (δ : TVarRename Γ Δ f id) :
  SubtypeP Γ T1 T2 ->
  SubtypeP Δ (T1.rename f id) (T2.rename f id) := by
  intro h
  apply SubtypeP.rec
        (motive_1 := 
          fun Γ T1 T2 _ => 
            ∀ {n2} {Δ : Ctx n2 _} {f} {_ : VarSubst Γ Δ f} {_ : TVarRename Γ Δ f id}, Subtype Δ (T1.rename f id) (T2.rename f id))
        (motive_2 := 
          fun Γ S1 S2 _ =>
            ∀ {n2} {Δ : Ctx n2 _} {f} {_ : VarSubst Γ Δ f} {_ : TVarRename Γ Δ f id}, SubtypeP Δ (S1.rename f id) (S2.rename f id))
    <;> try assumption
  case capt => 
    intros
    simp [CType.rename]
    apply Subtype.capt
    apply Subcapt.subst <;> aesop
    aesop
  case refl =>
    intros; constructor
  case trans =>
    intros
    apply SubtypeP.trans <;> aesop
  case top =>
    intros; simp [PType.rename]; apply SubtypeP.top
  case tvar =>
    intros
    simp [PType.rename]
    apply SubtypeP.tvar
    rename_i hb _ _ _ _ δ
    have h1 := δ hb
    exact h1
  case arr =>
    intros; rename_i ih1 ih2 _ _ f σ δ
    simp [PType.rename]
    apply SubtypeP.arr
    aesop
    apply ih2
    apply VarSubst.ext_var; trivial
    apply TVarRename.ext_var; trivial
  case tarr =>
    intros; rename_i ih1 ih2 _ _ f σ δ
    simp [PType.rename]
    apply SubtypeP.tarr
    aesop
    apply ih2
    apply VarSubst.ext_tvar; trivial
    rw [<- id_ext]
    apply TVarRename.ext_tvar; trivial
  case boxed =>
    intros; rename_i ih _ _ f σ δ
    simp [PType.rename]
    apply SubtypeP.boxed
    aesop

def Subtype.subst (h : Subtype Γ T1 T2) (σ : VarSubst Γ Δ f) (δ : TVarRename Γ Δ f id) :
  Subtype Δ (T1.rename f id) (T2.rename f id) := by
  cases h
  constructor
  apply Subcapt.subst <;> aesop
  apply SubtypeP.subst <;> aesop

def Subtype.narrow_var (hsub : Subtype Γ T1 T2)
  (h0 : Subtype (Ctx.extend_var Γ T2) U1 U2) :
  Subtype (Ctx.extend_var Γ T1) U1 U2 := by
  have h := Subtype.subst h0 (VarSubst.narrowing_var hsub) TVarRename.narrowing_var
  rw [<- CType.rename_id (T := U1)]
  rw [<- CType.rename_id (T := U2)]
  exact h
