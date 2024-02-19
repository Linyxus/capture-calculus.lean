import Mathlib.Data.Finset.Basic

import CC.Basic
import CC.CaptureSet
import CC.Context
import CC.Type

namespace CC

inductive Subcapt : Ctx n m -> CaptureSet n -> CaptureSet n -> Prop where
| sc_trans :
  Subcapt Γ C1 C2 ->
  Subcapt Γ C2 C3 ->
  Subcapt Γ C1 C3
| sc_elem :
  x ∈ C ->
  Subcapt Γ {x} C
| sc_elem_reach : ∀ {C : CaptureSet n},
  x ∈ C.reachElems ->
  Subcapt Γ ⟨ ∅ , {x} , false ⟩ C
| sc_elem_cap :
  Subcapt Γ {cap} ⟨ xs , rs , true ⟩
| sc_var :
  BoundVar Γ x (CType.capt C S) ->
  Subcapt Γ {x} C
| sc_set :
  (∀ x, x ∈ C1 -> Subcapt Γ {x} C2) ->
  (∀ x, mem_reach x C1 -> Subcapt Γ ⟨ ∅ , {x} , false ⟩ C2) ->
  (C1.isUniversal -> Subcapt Γ {cap} C2) ->
  Subcapt Γ C1 C2
| sc_reach :
  Subcapt Γ {x} ⟨∅, {x}, false⟩
| sc_reach_cap :
  Subcapt Γ ⟨∅, {x}, false⟩ {cap}
