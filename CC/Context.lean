import CC.CaptureSet
import CC.Basic
import CC.Type

namespace CC

inductive Ctx : Nat -> Nat -> Type where
| empty : Ctx 0 0
| extend_var :
  Ctx n m ->
  SepDegree n ->
  CType n m ->
  Ctx n.succ m
| extend_tvar :
  Ctx n m ->
  PType n m ->
  Ctx n m.succ

inductive BoundVar : Ctx n m -> Fin n -> SepDegree n -> CType n m -> Prop where
| here :
  BoundVar (Ctx.extend_var Γ D T) 0 D.weaken_var T.weaken_var
| there_var :
  BoundVar Γ x D T ->
  BoundVar (Ctx.extend_var Γ D' T') x.succ D.weaken_var T.weaken_var
| there_tvar :
  BoundVar Γ x D T ->
  BoundVar (Ctx.extend_tvar Γ S) x D T.weaken_tvar

inductive BoundTVar : Ctx n m -> Fin m -> PType n m -> Prop where
| here :
  BoundTVar (Ctx.extend_tvar Γ S) 0 S.weaken_tvar
| there_var :
  BoundTVar Γ x S ->
  BoundTVar (Ctx.extend_var Γ D T) x S.weaken_var
| there_tvar :
  BoundTVar Γ x S ->
  BoundTVar (Ctx.extend_tvar Γ S') x.succ S.weaken_tvar

def BoundVar.pred'
  {Γ : Ctx n m} {P : CType n m} {T : CType n.succ m} :
  Γ0 = Ctx.extend_var Γ D' P ->
  x0 = x.succ ->
  BoundVar Γ0 x0 D T ->
  ∃ T0 D0, T = T0.weaken_var ∧ D = D0.weaken_var ∧ BoundVar Γ x D0 T0 := by
  intro he1 he2 h
  cases h <;> try (solve | cases he1 | cases he2)
  cases he1
  simp [Fin.succ_inj] at he2
  subst_vars
  aesop

def BoundVar.pred
  {Γ : Ctx n m} {P : CType n m} {T : CType n.succ m} :
  BoundVar (Ctx.extend_var Γ D' P) x.succ D T ->
  ∃ T0 D0, T = T0.weaken_var ∧ D = D0.weaken_var ∧ BoundVar Γ x D0 T0 := by
  intro h
  apply BoundVar.pred' <;> aesop
