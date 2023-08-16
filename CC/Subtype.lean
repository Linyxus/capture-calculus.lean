import Mathlib.Data.Finset.Basic

import CC.Basic
import CC.CaptureSet
import CC.Context
import CC.Type

import CC.Subcapt

namespace CC

mutual

inductive Subtype : Ctx n m -> CType n m -> CType n m -> Prop where
| capt :
  Subcapt Γ C1 C2 ->
  SubtypeP Γ S1 S2 ->
  Subtype Γ (CType.capt C1 S1) (CType.capt C2 S2)

inductive SubtypeP : Ctx n m -> PType n m -> PType n m -> Prop where
| refl :
  SubtypeP Γ S S
| trans :
  SubtypeP Γ S1 S2 ->
  SubtypeP Γ S2 S3 ->
  SubtypeP Γ S1 S3
| top :
  SubtypeP Γ S PType.top
| tvar :
  BoundTVar Γ X S ->
  SubtypeP Γ (PType.tvar X) S
| arr :
  Subtype Γ T2 T1 ->
  Subtype (Ctx.extend_var Γ T2) U1 U2 ->
  SubtypeP Γ (PType.arr D T1 U1) (PType.arr D T2 U2)
| tarr :
  SubtypeP Γ S2 S1 ->
  Subtype (Ctx.extend_tvar Γ S2) T1 T2 ->
  SubtypeP Γ (PType.tarr S1 T1) (PType.tarr S2 T2)
| boxed :
  Subtype Γ T1 T2 ->
  SubtypeP Γ (PType.boxed T1) (PType.boxed T2)

end
