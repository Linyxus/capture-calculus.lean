import Mathlib.Data.Finset.Basic

import CC.Basic
import CC.CaptureSet
import CC.Context
import CC.Type
import CC.Subcapt

namespace CC

inductive Sep : Ctx n m -> CaptureSet n -> CaptureSet n -> Prop where
| symm :
  Sep Γ C1 C2 ->
  Sep Γ C2 C1
| set :
  (∀ x, x ∈ C1 -> Sep Γ {x} C2) ->
  (C1.hasRdr -> Sep Γ rdr C2) ->
  (C1.hasCap -> Sep Γ cap C2) ->
  Sep Γ C1 C2
| degree :
  BoundVar Γ x D T ->
  y ∈ D ->
  Sep Γ {x} {y} 
| degree_uniq :
  BoundVar Γ x SepDegree.uniq T ->
  x ≠ y ->
  Sep Γ {x} {y}
| var :
  BoundVar Γ x D (CType.capt C S) ->
  Sep Γ C C' ->
  Sep Γ {x} C'
| reader :
  Subcapt Γ {x1} { elems := {}, rdr := true, cap := false } ->
  Subcapt Γ {x2} { elems := {}, rdr := true, cap := false } ->
  Sep Γ {x1} {x2}
