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
| sc_var :
  BoundVar Γ x (CType.capt C S) ->
  Subcapt Γ {x} C
| sc_set :
  (∀ x, x ∈ C1 -> Subcapt Γ {x} C2) ->
  Subcapt Γ C1 C2
