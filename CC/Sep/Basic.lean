import Mathlib.Data.Finset.Basic

import CC.Basic
import CC.CaptureSet
import CC.Context
import CC.Type
import CC.Subcapt
import CC.Sep

namespace CC

lemma Sep.subcapt_pres_motive (Γ : Ctx n m) (C1 C2 : CaptureSet n) : Prop :=
  (∀ C', Subcapt Γ C' C1 -> Sep Γ C' C2) ∧
  (∀ C', Subcapt Γ C' C2 -> Sep Γ C1 C')

lemma Sep.elem_inv_motive (Γ : Ctx n m) (C1 C2 : CaptureSet n) : Prop :=
  (∀ x, x ∈ C1 -> Sep Γ {x} C2) ∧
  Sep Γ C1.rdrSet C2 ∧
  Sep Γ C1.capSet C2

lemma Sep.elem_inv' (h : Sep Γ C1 C2) :
  elem_inv_motive Γ C1 C2 ∧ elem_inv_motive Γ C2 C1 := by
  induction h <;> unfold elem_inv_motive at *
  case symm => aesop
  case set ihs ihr ihc =>
    apply And.intro
    · aesop
    · apply And.intro <;> try apply And.intro
      · intros x hx
        apply symm
        apply set
        · intros y hy
          have h1 := ihs y hy
          have ⟨_, ⟨h2, _⟩⟩ := h1
          apply symm; aesop
        · let ⟨_, h1, _⟩ := ihr
          apply symm; aesop
        · let ⟨_, h1, _⟩ := ihc
          apply symm; aesop
      · apply symm; apply set
        · intros y hy
          have h1 := ihs y hy
          have ⟨_, _, h2, _⟩ := h1
          apply symm; aesop
        · let ⟨_, _, h1, _⟩ := ihr
          apply symm; aesop
        · let ⟨_, _, h1, _⟩ := ihc
          apply symm; aesop
      · apply symm; apply set
        · intros y hy
          have h1 := ihs y hy
          have ⟨_, _, _, h2⟩ := h1
          apply symm; aesop
        · let ⟨_, _, _, h1⟩ := ihr
          apply symm; aesop
        · let ⟨_, _, _, h1⟩ := ihc
          apply symm; aesop
  case degree =>
    apply And.intro
    · apply And.intro <;> try apply And.intro
      · intros x hx
        simp at hx; subst_vars; apply degree <;> aesop
      · simp; apply empty
      · simp; apply empty
    · apply And.intro <;> try apply And.intro
      · intros x hx
        simp at hx; subst_vars; apply symm; apply degree <;> trivial
      · simp; apply empty
      · simp; apply empty
  case var hb hsep ih =>
    apply And.intro
    · apply And.intro <;> try apply And.intro
      · intros x hx
        simp at hx; subst_vars; apply var <;> trivial
      · simp; apply empty
      · simp; apply empty
    · apply And.intro <;> try apply And.intro
      · intros x hx
        apply symm; apply var; trivial
        apply symm; aesop
      · apply symm; apply var; trivial
        apply symm; aesop
      · apply symm; apply var; trivial
        apply symm; aesop 
  case reader =>
    apply And.intro
    · apply And.intro <;> try apply And.intro
      · intros x hx
        simp at hx; subst_vars; apply reader <;> trivial
      · simp; apply empty
      · simp; apply empty
    · apply And.intro <;> try apply And.intro
      · intros x hx
        simp at hx; subst_vars; apply symm; apply reader <;> trivial
      · simp; apply empty
      · simp; apply empty
  case empty =>
    apply And.intro
    · apply And.intro <;> try apply And.intro
      · intros x hx; cases hx
      · simp; apply empty
      · simp; apply empty
    · apply And.intro <;> try apply And.intro <;> try (solve | apply symm; apply empty)
      intros x _; apply symm; apply empty

lemma Sep.elems_inv (h : Sep Γ C1 C2) (he : x ∈ C1) : Sep Γ {x} C2 := by
  have h0 := Sep.elem_inv' h
  unfold elem_inv_motive at h0
  aesop

lemma Sep.rdr_elem_inv (h : Sep Γ C1 C2) : Sep Γ C1.rdrSet C2 := by
  have h0 := Sep.elem_inv' h
  unfold elem_inv_motive at h0
  aesop

lemma Sep.cap_elem_inv (h : Sep Γ C1 C2) : Sep Γ C1.capSet C2 := by
  have h0 := Sep.elem_inv' h
  unfold elem_inv_motive at h0
  aesop

def Sep.narrow_cap_motive (Γ : Ctx n m) (C1 C2 : CaptureSet n) : Prop :=
  (C1 = { elems := {}, cap := true, rdr := false } → ∀ C, Sep Γ C C2) ∧
  (C2 = { elems := {}, cap := true, rdr := false } → ∀ C, Sep Γ C1 C)

lemma Sep.narrow_cap'
  (h : Sep Γ C1 C2) : narrow_cap_motive Γ C1 C2 := by
  induction h <;> unfold narrow_cap_motive at *
  case symm ih => apply And.intro <;> try (solve | intros; apply symm; aesop)
  case set ihs ihr ihc =>
    apply And.intro
    · intros he C; subst_vars
      have ⟨ih, _⟩ := ihc
      apply ih; rfl  
    · intros he C
      apply set <;> aesop
  case empty => apply And.intro <;> (intros he C; (solve | cases he | apply empty))
  case var hb hsep ih =>
    apply And.intro <;> intros he C
    · rw [CaptureSet.singleton_def'] at he
      have he1 := CaptureSet.cap_val_eq he
      rw [CaptureSet.cap_val_def] at he1; rw [CaptureSet.cap_val_def] at he1
      cases he1
    · apply var; trivial; aesop
  case degree hb hd =>
    apply And.intro <;> (intros he C; exfalso; apply CaptureSet.singleton_eq_empty_absurd he)
  case reader =>
    apply And.intro <;> (intros he C; exfalso; apply CaptureSet.singleton_eq_empty_absurd he)

lemma Sep.narrow_cap
  (h : Sep Γ { elems := {}, rdr := false, cap := true} C2) :
  Sep Γ C1 C2 := by
  have h := Sep.narrow_cap' h; unfold narrow_cap_motive at h
  aesop

lemma Sep.rdr_spec_motive (Γ : Ctx n m) (C1 C2 : CaptureSet n) : Prop :=
  (C1 = { elems := {}, rdr := true, cap := false } → ∀ x D C S, BoundVar Γ x D (CType.capt C S) → IsReader Γ S → Sep Γ {x} C2) ∧
  (C2 = { elems := {}, rdr := true, cap := false } → ∀ x D C S, BoundVar Γ x D (CType.capt C S) → IsReader Γ S → Sep Γ C1 {x})

lemma Sep.rdr_spec' (h : Sep Γ C1 C2) : rdr_spec_motive Γ C1 C2 := by
  induction h <;> unfold rdr_spec_motive at *
  case symm => apply And.intro <;> try (solve | intros; apply symm; aesop)
  case set ihs ihr ihc => 
    apply And.intro
    · intros he x D C S hb hr; subst_vars
      have ⟨ih, _⟩ := ihr
      apply ih <;> aesop
    · intros he x D C S hb hr
      apply set
      · intros y hy
        have ⟨_, h1⟩ := ihs y hy
        apply h1 <;> trivial
      · aesop
      · aesop
  case empty => 
    apply And.intro <;> try (solve | intros he; cases he)
    intros; apply empty
  case var ih =>
    apply And.intro <;> intros he x D C S hb hr
    · exfalso; apply CaptureSet.singleton_eq_empty_absurd he
    · apply var; trivial; aesop 
  case degree =>
    apply And.intro <;> (intros he C; exfalso; apply CaptureSet.singleton_eq_empty_absurd he)
  case reader =>
    apply And.intro <;> (intros he C; exfalso; apply CaptureSet.singleton_eq_empty_absurd he)

lemma Sep.rdr_spec
  (h : Sep Γ { elems := {}, rdr := true, cap := false } C2)
  (hb : BoundVar Γ x D (CType.capt C S))
  (hr : IsReader Γ S) :
  Sep Γ {x} C2 := by
  have h := Sep.rdr_spec' h; unfold rdr_spec_motive at h
  aesop

lemma Sep.subcapt_pres (h : Sep Γ C1 C2) (hsub : Subcapt Γ C0 C1) : Sep Γ C0 C2 := by
  induction hsub
  case sc_trans ih1 ih2 => aesop
  case sc_elem h => apply Sep.elems_inv <;> trivial
  case sc_elem_rdr => apply Sep.rdr_elem_inv h
  case sc_elem_cap => apply Sep.cap_elem_inv h
  case sc_var h => apply var <;> trivial
  case sc_set ihs ihr ihc => apply set <;> aesop
  case sc_rdr_cap => apply narrow_cap h
  case sc_reader => apply rdr_spec h <;> trivial
