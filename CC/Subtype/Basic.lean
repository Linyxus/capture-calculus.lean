import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

import CC.Basic
import CC.Rename

import CC.CaptureSet
import CC.Context
import CC.Type
import CC.Subcapt
import CC.Subcapt.Basic
import CC.Subcapt.Rename
import CC.Subtype

namespace CC

def SubtypeP.tvar_inv_motive (Γ : Ctx n m) (S1 S2 : PType n m) : Prop :=
  ∀ X, 
    S2 = PType.tvar X ->
    SubtypeP Γ S1 S2 ->
    ∃ Y, S1 = PType.tvar Y

def SubtypeP.tvar_inv' :
  SubtypeP Γ S1 S2 ->
  SubtypeP.tvar_inv_motive Γ S1 S2 := by
  intro h
  apply SubtypeP.rec
    (motive_1 := fun Γ T1 T2 _ => True)
    (motive_2 := fun Γ S1 S2 _ => SubtypeP.tvar_inv_motive Γ S1 S2)
    <;> try (solve | trivial | intros; trivial | intros; unfold tvar_inv_motive; intros _ he; cases he)
  case refl =>
    intros; unfold tvar_inv_motive
    intros X he h
    aesop
  case trans =>
    intros; unfold tvar_inv_motive at *
    intros X he h
    rename_i h1 h2 ih1 ih2
    subst_vars
    have ih2' := ih2 _ rfl h2
    cases ih2'
    subst_vars
    apply ih1 <;> trivial
  case tvar => 
    intros; unfold tvar_inv_motive at *
    aesop

lemma SubtypeP.tvar_inv :
  SubtypeP Γ S1 (PType.tvar X2) ->
  ∃ X1, S1 = PType.tvar X1 := by
  intro h
  apply SubtypeP.tvar_inv' <;> trivial

theorem Subtype.refl :
  Subtype Γ T T := by
  cases T
  constructor
  apply Subcapt.refl
  apply SubtypeP.refl

theorem Subtype.trans
  (h1 : Subtype Γ T1 T2)
  (h2 : Subtype Γ T2 T3) :
  Subtype Γ T1 T3 := by
  cases h1
  cases h2
  constructor
  apply Subcapt.sc_trans <;> trivial
  apply SubtypeP.trans <;> trivial

def IsReader.subtype_pres_motive (Γ : Ctx n m) (S1 S2 : PType n m) : Prop :=
  IsReader Γ S2 ->
  IsReader Γ S1

theorem IsReader.subtype_pres'
  (hsub : SubtypeP Γ S' S) :
  subtype_pres_motive Γ S' S := by
  apply SubtypeP.rec
    (motive_1 := fun Γ T1 T2 _ => True)
    (motive_2 := fun Γ S1 S2 _ => subtype_pres_motive Γ S1 S2) <;>
    try (solve | intros; trivial | unfold subtype_pres_motive; intros; rename_i h; cases h)
  case refl => unfold subtype_pres_motive; intros; aesop
  case trans => unfold subtype_pres_motive; intros; aesop
  case tvar => 
    unfold subtype_pres_motive; intros
    constructor <;> aesop

theorem IsReader.subtype_pres
  (hsub : SubtypeP Γ S' S)
  (hreader : IsReader Γ S) :
  IsReader Γ S' := by
  apply subtype_pres' <;> trivial
