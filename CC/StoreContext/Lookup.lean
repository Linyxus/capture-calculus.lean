import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

import CC.Basic
import CC.Rename

import CC.CaptureSet
import CC.Context
import CC.Term
import CC.Type
import CC.Typed
import CC.Typed.Basic
import CC.Typed.Rename
import CC.EvalContext
import CC.StoreContext.Basic
import CC.Typed.CanonicalForm

namespace CC

theorem lookup_fun
  (hs : TypedStore γ Γ)
  (hx : Typed Γ (Term.var x) Cx (CType.capt Cf (PType.arr T U)))
  (hl : LookupStore γ x ⟨Term.abs T' t, hval⟩) :
  ∃ C0, Typed (Ctx.extend_var Γ T) t C0 U := by
  have h1 := Typed.var_typing_bound hx
  let ⟨C1, S1, hb, hsub⟩ := h1
  have h2 := lookup_store_typing hs hb hl
  let ⟨C2, ht⟩ := h2
  simp at ht
  apply Typed.cf_fun
  apply Typed.sub
  exact ht
  constructor
  apply Subcapt.refl
  exact hsub
