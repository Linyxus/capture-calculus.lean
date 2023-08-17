import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

import CC.Basic
import CC.Rename

import CC.CaptureSet
import CC.Context
import CC.EvalContext
import CC.Term
import CC.Term.TypeSubst
import CC.Type
import CC.Reduction
import CC.StoreContext.Lookup
import CC.Typed.Basic
import CC.Typed.Opening
import CC.Subtype.Subst

namespace CC

inductive Match : Ctx n1 m1 -> CType n1 m1 -> Ctx n2 m2 -> CType n2 m2 -> Prop where
| same :
  Match Γ T Γ T
| weaken :
  Match Γ T (Ctx.extend_var Γ {} P) T.weaken_var

theorem preservation :
  TypedState st1 Γ1 T1 ->
  Reduce st1 st2 ->
  ∃ Γ2 T2, TypedState st2 Γ2 T2 ∧ Match Γ1 T1 Γ2 T2 := by
  intro ht hr
  induction hr generalizing T1
  case red_app hl =>
    cases ht; rename_i hs hv
    have h1 := Typed.app_inv hv
    let ⟨Cx, Cy, Cf, T, U0, hx, hy, hsub⟩ := h1
    have h2 := lookup_fun hs hx hl
    let ⟨C2, ht⟩ := h2
    have h3 := Typed.var_typing_captures hy
    subst_vars
    have h4 := Typed.open_var hy ht
    apply Exists.intro Γ1; apply Exists.intro T1
    constructor
    constructor; trivial
    apply Typed.sub
    exact h4
    trivial
    constructor
  case red_tapp hl =>
    cases ht; rename_i hs hv
    have h1 := Typed.tapp_inv hv
    let ⟨Cx, Cf, U0, hx, hsub⟩ := h1
    have h2 := lookup_tfun hs hx hl
    let ⟨C2, ht⟩ := h2
    have h3 := Typed.open_tvar SubtypeP.refl ht
    apply Exists.intro Γ1; apply Exists.intro T1
    constructor
    constructor; trivial
    apply Typed.sub
    exact h3
    trivial
    constructor
  case red_open hl =>
    cases ht with
    | state hs hv =>
      have h1 := Typed.unbox_inv hv
      let ⟨Cx, Cf, hx⟩ := h1
      have h2 := lookup_box hs hx hl
      let ⟨C2, hy⟩ := h2
      apply Exists.intro Γ1; apply Exists.intro T1
      constructor
      constructor; trivial
      trivial
      constructor
  case red_rename =>
    let ⟨hs, hv⟩ := ht
    have h1 := Typed.let_inv hv
    let ⟨Ct, Cu, T, U0, U1, hx, ht, heq, hs, _⟩ := h1
    cases heq
    have h2 := Typed.var_typing_captures hx
    cases h2
    have h3 := Typed.open_var hx ht
    unfold CType.open_var at h3
    unfold CType.weaken_var at h3
    simp [CType.rename_comp] at h3
    apply Exists.intro Γ1; apply Exists.intro T1
    apply And.intro
    constructor; trivial
    apply Typed.sub <;> assumption
    constructor
  case red_liftval t v =>
    let ⟨hs, hv⟩ := ht
    have h1 := Typed.let_inv hv
    let ⟨Ct, Cu, T, U0, U1, hx, ht, heq, hs, hh⟩ := h1
    cases heq
    apply Exists.intro; apply Exists.intro T1.weaken_var
    constructor
    constructor
    constructor <;> trivial
    apply Typed.sub
    trivial
    apply Subtype.weaken_var; trivial
    constructor
  case red_ctx1 ih =>
    let ⟨hts, hv⟩ := ht 
    have h1 := Typed.let_inv hv
    let ⟨Ct, Cu, T, U0, U1, ht, hu, heq, hsub, hh, hh1⟩ := h1
    cases heq
    have hts' := TypedState.state hts ht
    have ih' := ih hts'
    let ⟨Γ2, T2, ⟨hts'', ht'⟩, hm⟩ := ih'
    cases hm with
    | same => 
      have ⟨C', hh'⟩ := hh _ _ ht'
      have h0 := TypedState.state hts'' hh'
      apply Exists.intro Γ1
      apply Exists.intro T1
      apply And.intro
      · assumption
      · constructor 
  case red_ctx2 ih =>
    let ⟨hts, hv⟩ := ht
    have h1 := Typed.let_inv hv
    let ⟨Ct, Cu, T, U0, U1, ht, hu, heq, hsub, hh, hh1⟩ := h1
    cases heq
    have hts' := TypedState.state hts ht
    have ih' := ih hts'
    let ⟨Γ2, T2, ⟨hts'', ht'⟩, hm⟩ := ih'
    cases hm with
    | weaken => 
      rename_i P0
      have ⟨C', hh'⟩ := hh1 _ _ P0 ht'
      have h0 := TypedState.state hts'' hh'
      repeat apply Exists.intro
      apply And.intro
      · exact h0
      · constructor

inductive Answer : Term n m -> Prop where
| val :
  Value t ->
  Answer t
| var :
  Answer (Term.var x)

-- A wrapper judgement to make induction work
inductive Reduce' : Store n -> Term n m -> Store n' -> Term n' m' -> Prop where
| reduce :
  Reduce ⟨γ, t⟩ ⟨γ', t'⟩ ->
  Reduce' γ t γ' t'

lemma lookup_store_result
  (hst : TypedStore γ Γ)
  (hx : Typed Γ (Term.var x) Cx (CType.capt C S)) :
  ∃ v C0 C', LookupStore γ x v ∧ Typed Γ v.t C0 (CType.capt C' S) := by
  have h1 := Typed.var_typing_bound hx
  let ⟨D1, C1, S1, hb, hsub1⟩ := h1; clear h1
  have h2 := lookup_store_exists γ x
  let ⟨v, hl⟩ := h2; clear h2
  have h3 := lookup_store_typing hst hb hl
  let ⟨C2, ht⟩ := h3; clear h3
  repeat apply Exists.intro
  constructor; assumption
  apply Typed.sub; assumption
  constructor; apply Subcapt.refl; trivial

theorem progress
  (ht : Typed Γ t C T)
  (hst : TypedStore γ Γ) :
  Answer t ∨ ∃ (n' m' : Nat) (γ' : Store n') (t' : Term n' m'), Reduce' γ t γ' t' := by
  induction ht <;> try (solve | apply Or.inl; apply Answer.val; constructor | apply Or.inl; apply Answer.var)
  case sub ih => apply ih; trivial
  case app hx hy _ _ => 
    have hz := TypedStore.no_tvar hst; subst_vars
    have h0 := lookup_store_result hst hx
    let ⟨⟨t, hv⟩, C0, C', hl, ht⟩ := h0; clear h0
    have h1 := Typed.val_inv_fun hv ht
    let ⟨u1, u2, he⟩ := h1; clear h1
    subst_vars
    apply Or.inr
    repeat apply Exists.intro
    constructor
    apply Reduce.red_app; trivial
  case tapp hx _ =>
    have hz := TypedStore.no_tvar hst; subst_vars
    have h0 := lookup_store_result hst hx
    let ⟨⟨t, hv⟩, C0, C', hl, ht⟩ := h0; clear h0
    have h1 := Typed.val_inv_tfun hv ht
    let ⟨u1, u2, he⟩ := h1; clear h1
    subst_vars
    apply Or.inr
    repeat apply Exists.intro
    constructor
    apply Reduce.red_tapp; trivial
  case unbox hx _ => 
    have hz := TypedStore.no_tvar hst; subst_vars
    have h0 := lookup_store_result hst hx
    let ⟨⟨t, hv⟩, C0, C', hl, ht⟩ := h0; clear h0
    have h1 := Typed.val_inv_box hv ht
    let ⟨x0, he⟩ := h1; clear h1
    subst_vars
    apply Or.inr
    repeat apply Exists.intro
    constructor
    apply Reduce.red_open; trivial
  case letval1 ih1 _ =>
    have hz := TypedStore.no_tvar hst; subst_vars
    have ih := ih1 hst
    cases ih with
    | inl ih => 
      cases ih with
      | var =>
        apply Or.inr; repeat apply Exists.intro
        constructor
        apply Reduce.red_rename
      | val ih =>
        apply Or.inr; repeat apply Exists.intro
        constructor
        apply Reduce.red_liftval; trivial
    | inr ih =>
      let ⟨n0, m0, γ0, t0, ih⟩ := ih
      cases ih; rename_i ih
      have h1 := Reduce.store_step ih
      cases h1 with
      | same =>
        apply Or.inr; repeat apply Exists.intro
        constructor
        apply Reduce.red_ctx1; trivial
      | extend =>
        apply Or.inr; repeat apply Exists.intro
        constructor
        apply Reduce.red_ctx2; trivial
  case letval2 hv _ _ _ _ _ =>
    have hz := TypedStore.no_tvar hst; subst_vars
    apply Or.inr
    repeat apply Exists.intro
    constructor
    apply Reduce.red_liftval; trivial
