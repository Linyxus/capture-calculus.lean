import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

import CC.Basic
import CC.Rename

import CC.CaptureSet
import CC.Context
import CC.Type
import CC.Subcapt
import CC.Subcapt.Rename
import CC.Subtype

namespace CC

def SubtypeP.rename {Γ : Ctx n1 m1} {Δ : Ctx n2 m2} {T1 T2 : PType n1 m1} 
  (h : SubtypeP Γ T1 T2)
  {f : VarMap n1 n2} {g : VarMap m1 m2}
  (σ : VarRename Γ Δ f g) (δ : TVarRename Γ Δ f g) :
  SubtypeP Δ (T1.rename f g) (T2.rename f g) := by
  apply SubtypeP.rec
        (motive_1 := 
          fun Γ T1 T2 _ => 
            ∀ {n2 m2} {Δ : Ctx n2 m2} {f g} (_ : VarRename Γ Δ f g) (_ : TVarRename Γ Δ f g), Subtype Δ (T1.rename f g) (T2.rename f g))
        (motive_2 :=
          fun Γ T1 T2 _ => 
            ∀ {n2 m2} {Δ : Ctx n2 m2} {f g} (_ : VarRename Γ Δ f g) (_ : TVarRename Γ Δ f g), SubtypeP Δ (T1.rename f g) (T2.rename f g))
    <;> try assumption
  case capt =>
    intros; rename_i hc _ ih _ _ _ σ δ
    simp
    constructor
    apply Subcapt.rename <;> aesop
    aesop
  case refl =>
    intros
    constructor
  case trans =>
    intros; rename_i ih1 ih2 _ _ _ σ δ
    apply SubtypeP.trans <;> aesop
  case top =>
    intros
    simp [PType.rename]
    apply SubtypeP.top
  case tvar =>
    intros; rename_i hb _ _ _ _ δ
    simp [PType.rename]
    apply SubtypeP.tvar
    aesop
  case arr =>
    intros; rename_i ih1 ih2 _ _ Δ f g σ δ
    simp
    apply SubtypeP.arr
    aesop
    apply ih2
    apply σ.ext_var
    apply δ.ext_var
  case tarr =>
    intros; rename_i ih1 ih2 _ _ Δ f g σ δ
    simp
    apply SubtypeP.tarr
    aesop
    apply ih2
    apply σ.ext_tvar
    apply δ.ext_tvar
  case boxed =>
    intros; rename_i ih _ _ Δ f g σ δ
    simp
    apply SubtypeP.boxed
    aesop
  
def Subtype.rename {Γ : Ctx n1 m1} {Δ : Ctx n2 m2} {T1 T2 : CType n1 m1} 
  (h : Subtype Γ T1 T2)
  {f : VarMap n1 n2} {g : VarMap m1 m2}
  (σ : VarRename Γ Δ f g) (δ : TVarRename Γ Δ f g) :
  Subtype Δ (T1.rename f g) (T2.rename f g) := by
  cases h
  simp
  apply Subtype.capt
  apply Subcapt.rename <;> aesop
  apply SubtypeP.rename <;> aesop

def Subtype.weaken_var (h : Subtype Γ T1 T2) P :
  Subtype (Ctx.extend_var Γ P) T1.weaken_var T2.weaken_var :=
  h.rename (VarRename.weaken_var_map Γ P) (TVarRename.weaken_var_map Γ P)

def SubtypeP.weaken_var (h : SubtypeP Γ T1 T2) P :
  SubtypeP (Ctx.extend_var Γ P) T1.weaken_var T2.weaken_var :=
  h.rename (VarRename.weaken_var_map Γ P) (TVarRename.weaken_var_map Γ P)

def SubtypeP.weaken_tvar (h : SubtypeP Γ T1 T2) P :
  SubtypeP (Ctx.extend_tvar Γ P) T1.weaken_tvar T2.weaken_tvar :=
  h.rename (VarRename.weaken_tvar_map Γ P) (TVarRename.weaken_tvar_map Γ P)
