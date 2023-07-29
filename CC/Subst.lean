import Mathlib.Data.Fin.Basic
import CC.Basic
import CC.Type
import CC.Context

namespace CC

def OpenMap (n m : Nat) : Type :=
  Fin m.succ -> PType n m

def OpenMap.ext_var (σ : OpenMap n m) : OpenMap n.succ m :=
  fun x => (σ x).weaken_var

def OpenMap.ext_tvar (σ : OpenMap n m) : OpenMap n m.succ := by
  intro x
  cases x using Fin.cases with
  | H0 => exact PType.tvar 0
  | Hs x0 => exact (σ x0).weaken_tvar

def tvar_open_map (R : PType n m) : OpenMap n m := by
  intro x
  cases x using Fin.cases with
  | H0 => exact R
  | Hs x0 => exact PType.tvar x0
