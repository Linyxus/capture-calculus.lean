import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

import CC.Basic
import CC.Rename

import CC.CaptureSet
import CC.Context
import CC.EvalContext
import CC.Term
import CC.Term.TypeSubst
import CC.Type

namespace CC

structure State (n : Nat) where
  store : Store n
  expr  : Term n 0

inductive Reduce : State n -> State n' -> Prop where
| red_app :
  LookupStore γ x ⟨Term.abs T t, pv⟩ ->
  Reduce ⟨γ, Term.app x y⟩ ⟨γ, t.open_var y⟩
| red_tapp :
  LookupStore γ x ⟨Term.tabs S t, pv⟩ ->
  Reduce ⟨γ, Term.tapp x R⟩ ⟨γ, t.open_tvar R⟩
| red_open :
  LookupStore γ x ⟨Term.box y, pv⟩ ->
  Reduce ⟨γ, Term.unbox C x⟩ ⟨γ, Term.var y⟩
| red_rename :
  Reduce ⟨γ, Term.letval (Term.var x) t⟩ ⟨γ, t.open_var x⟩ 
| red_liftval :
  (v : Value t) ->
  Reduce ⟨γ, Term.letval t u⟩ ⟨Store.cons γ ⟨t, v⟩, u⟩ 
| red_ctx1 :
  Reduce ⟨γ, t⟩ ⟨γ, t'⟩ ->
  Reduce ⟨γ, Term.letval t u⟩ ⟨γ, Term.letval t' u⟩
| red_ctx2 :
  Reduce ⟨γ, t⟩ ⟨Store.cons γ v, t'⟩ ->
  Reduce ⟨γ, Term.letval t u⟩ ⟨Store.cons γ v, Term.letval t' u.weaken_var1⟩

inductive TypedState : State n -> Ctx n 0 -> CType n 0 -> Prop where
| state :
  TypedStore γ Γ ->
  Typed Γ t C T ->
  TypedState ⟨γ, t⟩ Γ T

inductive StoreStep : Store n -> Store n' -> Prop where
| same :
  StoreStep γ γ
| extend :
  StoreStep γ (Store.cons γ v)

lemma Reduce.store_step
  (h : Reduce ⟨γ, t⟩ ⟨γ', t'⟩) :
  StoreStep γ γ' := by cases h <;> (solve | apply StoreStep.same | apply StoreStep.extend)
