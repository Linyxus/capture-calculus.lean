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
| val : ∀ {n},
  Store n ->
  Val n 0 ->
  Store (n + 1)
| var : ∀ {n},
  Store n ->
  Val n 0 ->
  Store (n + 1)
| set : ∀ {n},
  Store n ->
  Fin n ->
  Val n 0 ->
  Store n

inductive Focus : Term n 0 -> Term n' 0 -> Type where
| this : (t : Term n 0) -> Focus t t
| val_left : ∀ {t : Term n 0} {t' : Term n' 0},
  (M : LetMode) ->
  Focus t t' ->
  (u : Term n.succ 0) ->
  Focus (Term.letval M t u) t'
| val_right : ∀ {u : Term (Nat.succ n) 0} {u' : Term n' 0},
  (t : Term n 0) ->
  Focus u u' ->
  Focus (Term.letval LetMode.par t u) u'

inductive Store.LookupVal : Store n -> Fin n -> Val n 0 -> Prop where
| here :
  Store.LookupVal (Store.val γ v) 0 v.weaken_var
| there_val :
  Store.LookupVal γ x v ->
  Store.LookupVal (Store.val γ v0) x.succ v.weaken_var
| there_var :
  Store.LookupVal γ x v ->
  Store.LookupVal (Store.var γ v0) x.succ v.weaken_var
| there_set :
  Store.LookupVal γ x v ->
  Store.LookupVal (Store.set γ y v0) x v

inductive Store.LookupVar : Store n -> Fin n -> Val n 0 -> Prop where
| here_var :
  Store.LookupVar (Store.var γ v) 0 v.weaken_var
| here_set :
  Store.LookupVar (Store.set γ x v) x v
| there_val :
  Store.LookupVar γ x v ->
  Store.LookupVar (Store.val γ v0) x.succ v.weaken_var
| there_var :
  Store.LookupVar γ x v ->
  Store.LookupVar (Store.var γ v0) x.succ v.weaken_var
| there_set :
  Store.LookupVar γ x v ->
  Store.LookupVar (Store.set γ y v0) x v

-- inductive LookupStore : ∀ {n}, Store n -> Fin n -> Val n 0 -> Prop where
-- | here :
--   LookupStore (Store.cons γ v) 0 v.weaken_var
-- | there :
--   LookupStore γ x v ->
--   LookupStore (Store.cons γ v0) x.succ v.weaken_var

-- inductive TypedStore : Store n -> Ctx n m -> Prop where
-- | empty :
--   TypedStore Store.empty Ctx.empty
-- | val :
--   TypedStore γ Γ ->
--   Typed Γ t C T ->
--   TypedStore (Store.val γ ⟨t, isVal⟩) (Ctx.extend_var Γ {} T)
-- | var :
--   TypedStore γ Γ ->
--   Typed Γ t C (CType.capt {} S) ->
--   TypedStore (Store.var γ ⟨t, isVal⟩) (Ctx.extend_var Γ {})

-- lemma TypedStore.no_tvar {γ : Store n} {Γ : Ctx n m}
--   (h : TypedStore γ Γ) :
--   m = 0 := by induction h <;> rfl
