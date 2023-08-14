import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

import CC.Basic
import CC.Rename

import CC.CaptureSet
import CC.Context
import CC.Term
import CC.Type
import CC.Typed

namespace CC

inductive Store : Nat -> Type where
| empty : Store 0
| cons : ∀ {n},
  Store n ->
  Val n 0 ->
  Store (n + 1)

inductive LookupStore : ∀ {n}, Store n -> Fin n -> Val n 0 -> Prop where
| here :
  LookupStore (Store.cons γ v) 0 v.weaken_var
| there :
  LookupStore γ x v ->
  LookupStore (Store.cons γ v0) x.succ v.weaken_var

inductive TypedStore : Store n -> Ctx n m -> Prop where
| empty :
  TypedStore Store.empty Ctx.empty
| cons :
  TypedStore γ Γ ->
  Typed Γ t C T ->
  TypedStore (Store.cons γ ⟨t, isVal⟩) (Ctx.extend_var Γ T)

lemma TypedStore.no_tvar {γ : Store n} {Γ : Ctx n m}
  (h : TypedStore γ Γ) :
  m = 0 := by induction h <;> rfl
