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
  (hx : BoundVar Γ x T r)
  (hl : LookupStore γ x v) :
  ∃ C, Typed Γ v.t C T := by
  induction hl
  case here =>
    cases hs
    case cons =>
      simp [Val.weaken_var]
      cases hx
      rename_i C T _ _ _ h
      have h' := h.weaken_var T (Region.var 0)
      apply Exists.intro
      apply h'
    case cons_empty =>
      simp [Val.weaken_var]
      cases hx
      rename_i C T _ _ _ h
      have h' := h.weaken_var T Region.glob
      apply Exists.intro
      apply h'
  case there ih =>
    cases hs
    case cons =>
      rename_i hs _ _ _ _
      have hx' := BoundVar.pred hx
      let ⟨T0, r0, ⟨hx1, hx0, hx2⟩⟩ := hx'
      clear hx'
      subst_vars
      have ih' := ih hs hx2
      cases ih'
      constructor
      apply Typed.weaken_var
      aesop
    case cons_empty =>
      rename_i hs _ _ _ _
      have hx' := BoundVar.pred hx
      let ⟨T0, r0, ⟨hx1, hx0, hx2⟩⟩ := hx'
      clear hx'
      subst_vars
      have ih' := ih hs hx2
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
