import Mathlib.Data.Fin.Basic
import Mathlib.Data.Vector
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

import CC0.Basic

namespace CC0

def CSet (n : Nat) : Type := Vector Bool n

mutual

inductive PType : Nat -> Nat -> Type where
| tvar : Fin m -> PType n m
| top : PType n m
| func : CType n m -> CType n.succ m -> PType n m
| poly : PType n m -> CType n m.succ -> PType n m
| boxed : CType n m -> PType n m

inductive CType : Nat -> Nat -> Type where
| capt : CSet n -> PType n m -> CType n m

end

def CSet.empty (n : Nat) : CSet n :=
  Vector.replicate n false

def CSet.union (C1 : CSet n) (C2 : CSet n) : CSet n :=
  Vector.map₂ (fun b1 b2 => b1 || b2) C1 C2

def CSet.singleton (i : Fin n) : CSet n :=
  Vector.ofFn (fun j => j == i)

def CSet.contains (C : CSet n) (i : Fin n) : Prop :=
  C.get i = true

def Fin.range (n : Nat) : Vector (Fin n) n :=
  Vector.ofFn (fun i => i)

def CSet.rename (C : CSet n) (f : VarMap n m) : CSet m := sorry
