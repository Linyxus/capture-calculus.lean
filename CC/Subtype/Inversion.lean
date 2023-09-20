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
import CC.Subtype.Basic
import CC.Subtype.Subst
import CC.Subtype.TypeSubst

namespace CC

private def SubtypeP.fun_inv_motive (Γ : Ctx n m) (S1 S2 : PType n m) : Prop :=
  ∀ D T U, 
    S2 = PType.arr D T U ->
    SubtypeP Γ S1 S2 ->
    (∃ X, S1 = PType.tvar X) ∨ 
    (∃ T' U', S1 = PType.arr D T' U' ∧ Subtype Γ T T' ∧ Subtype (Ctx.extend_var Γ D T) U' U)

lemma SubtypeP.fun_inv' :
  SubtypeP Γ S1 S2 ->
  SubtypeP.fun_inv_motive Γ S1 S2 := by
  intro h
  apply SubtypeP.rec
    (motive_1 := fun Γ T1 T2 _ => True)
    (motive_2 := fun Γ S1 S2 _ => SubtypeP.fun_inv_motive Γ S1 S2)
    <;> try (solve | trivial | intros; trivial | intros; unfold fun_inv_motive; intros _ _ _ he; cases he)
  case refl =>
    intros; unfold fun_inv_motive
    intros D T U he h
    subst_vars
    apply Or.inr
    repeat apply Exists.intro
    constructor
    rfl
    constructor <;> apply Subtype.refl
  case trans =>
    intros
    unfold fun_inv_motive at *
    intros D T U he h
    rename_i h1 h2 ih1 ih2
    have ih2' := ih2 _ _ _ he h2
    cases ih2'
    case inl ih =>
      let ⟨X0, he0⟩ := ih
      subst_vars
      have h1' := SubtypeP.tvar_inv h1
      aesop
    case inr ih =>
      let ⟨T', U', he, ih1, ih2⟩ := ih
      subst_vars
      have ih' := ih1 _ _ _ rfl h1
      cases ih'
      case inl => aesop
      case inr =>
        rename_i ih
        let ⟨T'', U'', he', ih1', ih2'⟩ := ih
        subst_vars
        apply Or.inr
        repeat apply Exists.intro
        constructor
        rfl
        constructor
        apply Subtype.trans <;> trivial
        apply Subtype.trans
        apply Subtype.narrow_var
        assumption
        assumption
        assumption
  case tvar =>
    intros
    unfold fun_inv_motive at *
    intros D T U he h
    subst_vars
    apply Or.inl
    apply Exists.intro
    rfl
  case arr =>
    intros
    unfold fun_inv_motive at *
    intros D T U he h
    subst_vars
    apply Or.inr
    repeat apply Exists.intro
    constructor
    cases he; rfl
    cases he
    constructor <;> trivial

theorem SubtypeP.fun_inv :
  SubtypeP Γ P (PType.arr D T U) ->
  (∃ X, P = PType.tvar X) ∨ 
  (∃ T' U', P = PType.arr D T' U' ∧ Subtype Γ T T' ∧ Subtype (Ctx.extend_var Γ D T) U' U) := by
  intros
  apply SubtypeP.fun_inv' <;> aesop

private def SubtypeP.tfun_inv_motive (Γ : Ctx n m) (S1 S2 : PType n m) : Prop :=
  ∀ T U, 
    S2 = PType.tarr T U ->
    SubtypeP Γ S1 S2 ->
    (∃ X, S1 = PType.tvar X) ∨ 
    (∃ T' U', S1 = PType.tarr T' U' ∧ SubtypeP Γ T T' ∧ Subtype (Ctx.extend_tvar Γ T) U' U)

lemma SubtypeP.tfun_inv' 
  (h : SubtypeP Γ S1 S2) :
  SubtypeP.tfun_inv_motive Γ S1 S2 := by
  apply SubtypeP.rec
    (motive_1 := fun Γ T1 T2 _ => True)
    (motive_2 := fun Γ S1 S2 _ => SubtypeP.tfun_inv_motive Γ S1 S2)
    <;> try (solve | trivial | intros; trivial | intros; unfold tfun_inv_motive; intros _ _ he; cases he)
  case refl =>
    intros; unfold tfun_inv_motive
    intros
    apply Or.inr
    repeat apply Exists.intro
    constructor
    trivial
    constructor
    apply SubtypeP.refl
    apply Subtype.refl
  case trans =>
    intros; unfold tfun_inv_motive at *
    intros T U he h
    rename_i h1 h2 ih1 ih2
    subst_vars
    have ih2' := ih2 _ _ rfl h2
    cases ih2'
    case inl ih =>
      let ⟨X0, he0⟩ := ih
      subst_vars
      have h1' := SubtypeP.tvar_inv h1
      aesop
    case inr ih =>
      let ⟨T', U', he, ih1, ih2⟩ := ih
      subst_vars
      have ih' := ih1 _ _ rfl h1
      cases ih'
      case inl => aesop
      case inr ih' =>
        let ⟨T'', U'', he', ih1', ih2'⟩ := ih'
        subst_vars
        apply Or.inr
        repeat apply Exists.intro
        constructor
        trivial
        constructor
        apply SubtypeP.trans <;> trivial
        apply Subtype.trans
        · apply Subtype.narrow_tvar <;> trivial
        · assumption
  case tvar =>
    intros; unfold tfun_inv_motive at *
    intros T U he h
    subst_vars
    apply Or.inl
    apply Exists.intro
    rfl
  case tarr =>
    intros; unfold tfun_inv_motive at *
    intros T U he h
    subst_vars
    apply Or.inr
    repeat apply Exists.intro
    constructor
    rfl
    cases he
    constructor <;> trivial

lemma SubtypeP.tfun_inv :
  SubtypeP Γ P (PType.tarr T U) ->
  (∃ X, P = PType.tvar X) ∨ 
  (∃ T' U', P = PType.tarr T' U' ∧ SubtypeP Γ T T' ∧ Subtype (Ctx.extend_tvar Γ T) U' U) := by
  intro h
  apply SubtypeP.tfun_inv' <;> aesop

private def SubtypeP.boxed_inv_motive (Γ : Ctx n m) (S1 S2 : PType n m) : Prop :=
  ∀ T, 
    S2 = PType.boxed T ->
    SubtypeP Γ S1 S2 ->
    (∃ X, S1 = PType.tvar X) ∨ 
    (∃ T', S1 = PType.boxed T' ∧ Subtype Γ T' T)

lemma SubtypeP.boxed_inv'
  (h : SubtypeP Γ S1 S2) :
  SubtypeP.boxed_inv_motive Γ S1 S2 := by
  apply SubtypeP.rec
    (motive_1 := fun Γ T1 T2 _ => True)
    (motive_2 := fun Γ S1 S2 _ => SubtypeP.boxed_inv_motive Γ S1 S2)
    <;> try (solve | trivial | intros; trivial | intros; unfold boxed_inv_motive; intros _ he; cases he)
  case refl =>
    intros; unfold boxed_inv_motive
    intros
    apply Or.inr
    repeat apply Exists.intro
    constructor
    trivial
    apply Subtype.refl
  case trans =>
    intros; unfold boxed_inv_motive at *
    intros T he h
    rename_i h1 h2 ih1 ih2
    subst_vars
    have ih2' := ih2 _ rfl h2
    cases ih2'
    case inl ih =>
      let ⟨X0, he0⟩ := ih
      subst_vars
      have h1' := SubtypeP.tvar_inv h1
      aesop
    case inr ih =>
      let ⟨T', he, ih1⟩ := ih
      subst_vars
      have ih' := ih1 _ rfl h1
      cases ih'
      case inl => aesop
      case inr ih' =>
        let ⟨T'', he', ih1'⟩ := ih'
        subst_vars
        apply Or.inr
        repeat apply Exists.intro
        constructor
        trivial
        apply Subtype.trans <;> trivial
  case tvar =>
    intros; unfold boxed_inv_motive at *
    intros T he h
    subst_vars
    apply Or.inl
    apply Exists.intro
    rfl
  case boxed =>
    intros; unfold boxed_inv_motive at *
    intros T he h
    subst_vars
    apply Or.inr
    repeat apply Exists.intro
    constructor
    trivial
    aesop

lemma SubtypeP.boxed_inv :
  SubtypeP Γ P (PType.boxed T) ->
  (∃ X, P = PType.tvar X) ∨ 
  (∃ T', P = PType.boxed T' ∧ Subtype Γ T' T) := by
  intro h
  apply SubtypeP.boxed_inv' <;> aesop
