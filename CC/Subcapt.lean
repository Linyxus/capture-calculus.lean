import Mathlib.Data.Finset.Basic

import CC.Basic
import CC.CaptureSet
import CC.Context
import CC.Type

namespace CC

inductive IsReader : Ctx n m -> PType n m -> Prop where
| reader :
  IsReader Γ (PType.reader S)
| widen :
  BoundTVar Γ X S ->
  IsReader Γ S ->
  IsReader Γ (PType.tvar X)

inductive Subcapt : Ctx n m -> CaptureSet n -> CaptureSet n -> Prop where
| sc_trans :
  Subcapt Γ C1 C2 ->
  Subcapt Γ C2 C3 ->
  Subcapt Γ C1 C3
| sc_elem :
  x ∈ C ->
  Subcapt Γ {x} C
| sc_elem_rdr :
  C.hasRdr ->
  Subcapt Γ rdr C
| sc_elem_cap :
  C.hasCap ->
  Subcapt Γ cap C
| sc_var :
  BoundVar Γ x D (CType.capt C S) ->
  Subcapt Γ {x} C
| sc_set :
  (∀ x, x ∈ C1 -> Subcapt Γ {x} C2) ->
  (C1.hasRdr -> Subcapt Γ rdr C2) ->
  (C1.hasCap -> Subcapt Γ cap C2) ->
  Subcapt Γ C1 C2
| sc_rdr_cap :
  Subcapt Γ rdr cap
| sc_reader :
  BoundVar Γ x D (CType.capt C S) ->
  IsReader Γ S ->
  Subcapt Γ {x} rdr
