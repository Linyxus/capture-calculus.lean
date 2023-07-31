import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

import CC.Basic
import CC.Rename

import CC.CaptureSet
import CC.Context
import CC.Term
import CC.Type
import CC.Typed
import CC.Typed.Rename
import CC.EvalContext

namespace CC

def BoundVar.pred'
  {Γ : Ctx n m} {P : CType n m} {T : CType n.succ m} :
  Γ0 = Ctx.extend_var Γ P ->
  x0 = x.succ ->
  BoundVar Γ0 x0 T ->
  ∃ T0, T = T0.weaken_var ∧ BoundVar Γ x T0 := by
  intro he1 he2 h
  cases h <;> try (solve | cases he1 | cases he2)
  cases he1
  simp [Fin.succ_inj] at he2
  subst_vars
  aesop

def BoundVar.pred
  {Γ : Ctx n m} {P : CType n m} {T : CType n.succ m} :
  BoundVar (Ctx.extend_var Γ P) x.succ T ->
  ∃ T0, T = T0.weaken_var ∧ BoundVar Γ x T0 := by
  intro h
  apply BoundVar.pred' <;> aesop

theorem lookup_store_typing
  (hs : TypedStore γ Γ)
  (hx : BoundVar Γ x T)
  (hl : LookupStore γ x v) :
  ∃ C, Typed Γ v.t C T := by
  induction hl
  case here =>
    cases hs
    simp [Val.weaken_var]
    cases hx
    rename_i C T _ h _
    have h' := h.weaken_var T
    apply Exists.intro
    apply h'
  case there ih =>
    cases hs
    rename_i hs
    have hx' := BoundVar.pred hx
    let ⟨T0, ⟨hx1, hx2⟩⟩ := hx'
    clear hx'
    subst_vars
    have ih' := ih hs hx2
    cases ih'
    constructor
    apply Typed.weaken_var
    aesop
