import Mathlib.Data.Fin.Basic

namespace CC

def VarMap (n m : Nat) : Type := Fin n -> Fin m

def extv (f : VarMap n m) : VarMap n.succ m.succ := by
  intro i
  cases i using Fin.cases with
  | H0 => exact 0
  | Hs i0 => exact (f i0).succ

def weaken_map : VarMap n n.succ := fun x => x.succ
