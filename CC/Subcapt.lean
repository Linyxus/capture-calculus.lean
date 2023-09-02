import Mathlib.Data.Finset.Basic

import CC.Basic
import CC.CaptureSet
import CC.Context
import CC.Type

namespace CC

inductive NonRoot : Ctx n m -> PType n m -> Prop where
| tvar :
  BoundTVar Γ X S ->
  NonRoot Γ S ->
  NonRoot Γ (PType.tvar X)
| top :
  NonRoot Γ (PType.top)
| arr :
  NonRoot Γ (PType.arr T U)
| tarr :
  NonRoot Γ (PType.tarr T U)
| boxed :
  NonRoot Γ (PType.boxed T)

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
  NonRoot Γ S ->
  Subcapt Γ {x} C
| sc_set :
  (∀ x, x ∈ C1 -> Subcapt Γ {x} C2) ->
  Subcapt Γ C1 C2
