import CC.CaptureSet
import CC.Basic
import CC.Type

namespace CC

inductive Region : Nat -> Type where
| var : Fin n -> Region n
| glob : Region n

def Region.rename (r : Region n1) (f : VarMap n1 n2) : Region n2 :=
  match r with
  | Region.var x => Region.var (f x)
  | Region.glob => Region.glob

def Region.weaken_var (r : Region n) : Region n.succ :=
  r.rename weaken_map

def Region.weaken_var1 (r : Region (Nat.succ n)) : Region (Nat.succ n).succ :=
  r.rename weaken_map.ext

def Region.weaken_var_glob_def :
  (Region.glob : Region n).weaken_var = Region.glob := by rfl

inductive Ctx : Nat -> Nat -> Type where
| empty : Ctx 0 0
| extend_var :
  Ctx n m ->
  CType n m ->
  Region n ->
  Ctx n.succ m
| extend_tvar :
  Ctx n m ->
  PType n m ->
  Ctx n m.succ

inductive BoundVar : Ctx n m -> Fin n -> CType n m -> Region n -> Prop where
| here :
  BoundVar (Ctx.extend_var Γ T r) 0 T.weaken_var r.weaken_var
| there_var :
  BoundVar Γ x T r ->
  BoundVar (Ctx.extend_var Γ T' r') x.succ T.weaken_var r.weaken_var
| there_tvar :
  BoundVar Γ x T r ->
  BoundVar (Ctx.extend_tvar Γ S) x T.weaken_tvar r

inductive BoundTVar : Ctx n m -> Fin m -> PType n m -> Prop where
| here :
  BoundTVar (Ctx.extend_tvar Γ S) 0 S.weaken_tvar
| there_var :
  BoundTVar Γ x S ->
  BoundTVar (Ctx.extend_var Γ T r) x S.weaken_var
| there_tvar :
  BoundTVar Γ x S ->
  BoundTVar (Ctx.extend_tvar Γ S') x.succ S.weaken_tvar

def BoundVar.pred'
  {Γ : Ctx n m} {P : CType n m} {T : CType n.succ m} :
  Γ0 = Ctx.extend_var Γ P p ->
  x0 = x.succ ->
  BoundVar Γ0 x0 T r ->
  ∃ T0 r0, T = T0.weaken_var ∧ r = r0.weaken_var ∧ BoundVar Γ x T0 r0 := by
  intro he1 he2 h
  cases h <;> try (solve | cases he1 | cases he2)
  cases he1
  simp [Fin.succ_inj] at he2
  subst_vars
  aesop

def BoundVar.pred
  {Γ : Ctx n m} {P : CType n m} {T : CType n.succ m} :
  BoundVar (Ctx.extend_var Γ P p) x.succ T r ->
  ∃ T0 r0, T = T0.weaken_var ∧ r = r0.weaken_var ∧ BoundVar Γ x T0 r0 := by
  intro h
  apply BoundVar.pred' <;> aesop

@[simp]
def Region.rename_id {r : Region n} :
  r.rename id = r := by
  cases r <;> rfl

theorem Region.rename_comp {r : Region n} :
  (r.rename f1).rename f2 = r.rename (f2.comp f1) := by
  cases r <;> unfold VarMap.comp <;> simp [rename]

lemma Region.weaken_var1_def {r : Region (Nat.succ n)} :
  r.weaken_var1 = r.rename weaken_map.ext := by simp [weaken_var1]
