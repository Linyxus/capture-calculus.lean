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
  Match Γ T (Ctx.extend_var Γ P) T.weaken_var

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
