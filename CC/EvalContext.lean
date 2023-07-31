import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

import CC.Basic
import CC.Rename

import CC.CaptureSet
import CC.Context
import CC.Term
import CC.Type

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
