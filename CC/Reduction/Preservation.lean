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

namespace CC

inductive Match : CType n1 m1 -> CType n2 m2 -> Prop where
| same :
  Match T T
| weaken :
  Match T.weaken_var T

theorem preservation :
  TypedState st1 T1 ->
  Reduce st1 st2 ->
  ∃ T2, TypedState st2 T2 ∧ Match T1 T2 := by
  intro ht hr
  induction hr
  case red_app hl =>
    cases ht; rename_i hs hv
    have h1 := Typed.app_inv hv
    let ⟨Cx, Cy, Cf, T, U0, hx, hy, hsub⟩ := h1
    have h2 := lookup_fun hs hx hl
    let ⟨C2, ht⟩ := h2
    have h3 := Typed.var_typing_captures hy
    subst_vars
    have h4 := Typed.open_var hy ht
    apply Exists.intro T1
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
    apply Exists.intro T1
    constructor
    constructor; trivial
    apply Typed.sub
    exact h3
    trivial
    constructor
  case red_open => sorry
  case red_rename => sorry
  case red_liftval => sorry
  case red_ctx => sorry
