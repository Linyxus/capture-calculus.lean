import CC.CaptureSet
import CC.Basic
import CC.Type

namespace CC

inductive Ctx : Nat -> Nat -> Type where
| empty : Ctx 0 0
| extend_var :
  Ctx n m ->
  CType n m ->
  Ctx n.succ m
| extend_tvar :
  Ctx n m ->
  PType n m ->
  Ctx n m.succ

inductive BoundVar : Ctx n m -> Fin n -> CType n m -> Type where
| here :
  BoundVar (Ctx.extend_var Γ T) 0 T.weaken_var
| there_var :
  BoundVar Γ x T ->
  BoundVar (Ctx.extend_var Γ T') x.succ T.weaken_var
| there_tvar :
  BoundVar Γ x T ->
  BoundVar (Ctx.extend_tvar Γ S) x T.weaken_tvar

inductive BoundTVar : Ctx n m -> Fin m -> PType n m -> Type where
| here :
  BoundTVar (Ctx.extend_tvar Γ S) 0 S.weaken_tvar
| there_var :
  BoundTVar Γ x S ->
  BoundTVar (Ctx.extend_var Γ T) x S.weaken_var
| there_tvar :
  BoundTVar Γ x S ->
  BoundTVar (Ctx.extend_tvar Γ S') x.succ S.weaken_tvar
