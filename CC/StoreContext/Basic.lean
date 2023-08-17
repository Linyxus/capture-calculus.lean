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

theorem lookup_store_typing
  (hs : TypedStore γ Γ)
  (hx : BoundVar Γ x D T)
  (hl : LookupStore γ x v) :
  ∃ C, Typed Γ v.t C T := by
  induction hl
  case here =>
    cases hs
    simp [Val.weaken_var]
    cases hx
    rename_i C T _ h _
    have h' := h.weaken_var (D := {}) T
    apply Exists.intro
    apply h'
  case there ih =>
    cases hs
    rename_i hs
    have hx' := BoundVar.pred hx
    let ⟨T0, D, ⟨hx1, hx2, hx3⟩⟩ := hx'
    clear hx'
    subst_vars
    have ih' := ih hs hx3
    cases ih'
    constructor
    apply Typed.weaken_var
    aesop

lemma lookup_store_exists (γ : Store n) (x : Fin n) :
  ∃ v, LookupStore γ x v := by
  induction γ
  case empty => cases x.isLt
  case cons γ v ih =>
    cases x using Fin.cases with
    | H0 => constructor; constructor
    | Hs x0 => 
      have ih' := ih x0; cases ih'
      constructor; constructor; assumption
