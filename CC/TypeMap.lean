import Mathlib.Data.Fin.Basic
import CC.Basic
import CC.Type
import CC.Context
import CC.Rename

namespace CC

def TypeMap (n m1 m2 : Nat) : Type :=
  Fin m1 -> PType n m2

def TypeMap.ext_var (σ : TypeMap n m1 m2) : TypeMap n.succ m1 m2 :=
  fun x => (σ x).weaken_var

def TypeMap.ext_tvar (σ : TypeMap n m1 m2) : TypeMap n m1.succ m2.succ := by
  intro x
  cases x using Fin.cases with
  | H0 => exact PType.tvar 0
  | Hs x0 => exact (σ x0).weaken_tvar

def TypeMap.then (σ : TypeMap n1 m1 m2) (f : VarMap n1 n2) (g : VarMap m2 m3) :
  TypeMap n2 m1 m3 := fun x => (σ x).rename f g

def TypeMap.compv (σ : TypeMap n m2 m3) (g : VarMap m1 m2) :
  TypeMap n m1 m3 := fun x => σ (g x)

def TypeMap.map (σ : TypeMap n m1 m2) (f : PType n m2 -> PType n m3) : TypeMap n m1 m3 :=
  fun x => f (σ x)

def tvar_open_map (R : PType n m) : TypeMap n m.succ m := by
  intro x
  cases x using Fin.cases with
  | H0 => exact R
  | Hs x0 => exact PType.tvar x0

theorem TypeMap.ext_var_then_comm (σ : TypeMap n m1 m2) :
  σ.ext_var.then f.ext g = (σ.then f g).ext_var := by
  funext x
  cases m1 with
  | zero =>
    exfalso
    let ⟨ _ , h ⟩ := x
    cases h
  | succ _ =>
    cases x using Fin.cases with
    | H0 =>
      simp [TypeMap.then, TypeMap.ext_var]
      simp [PType.rename_weaken_comm]
    | Hs x0 =>
      simp [TypeMap.then, TypeMap.ext_var]
      simp [PType.rename_weaken_comm]

theorem TypeMap.ext_tvar_then_comm (σ : TypeMap n m1 m2) :
  σ.ext_tvar.then f g.ext = (σ.then f g).ext_tvar := by
  funext x
  cases x using Fin.cases with
  | H0 =>
    simp [TypeMap.then, TypeMap.ext_tvar]
    simp [PType.rename_weaken_comm, PType.rename]
  | Hs x0 =>
    simp [TypeMap.then, TypeMap.ext_tvar]
    simp [PType.rename_weaken_tvar_comm, PType.rename]

theorem TypeMap.compv_ext_var_comm (σ : TypeMap n m1 m2) :
  (σ.compv g).ext_var = σ.ext_var.comp g := by aesop

theorem TypeMap.compv_ext_tvar_comm (σ : TypeMap n m1 m2) :
  (σ.compv g).ext_tvar = σ.ext_tvar.comp g.ext := by
  funext x
  cases x using Fin.cases with
  | H0 => 
    simp [VarMap.ext]
    simp [ext_tvar]
  | Hs x0 =>
    simp [VarMap.ext]
    simp [ext_tvar, compv]

theorem tvar_open_map_rename_comm 
  (R : PType n1 m1)
  {f : VarMap n1 n2} {g : VarMap m1 m2} :
  (tvar_open_map R).then f g = (tvar_open_map (R.rename f g)).compv g.ext := by
  funext x
  cases x using Fin.cases with
  | H0 => 
    conv =>
      lhs
      simp [TypeMap.then, tvar_open_map]
  | Hs x0 =>
    conv =>
      lhs
      simp [TypeMap.then, tvar_open_map]
    conv =>
      rhs
      simp [TypeMap.compv, VarMap.ext]
      simp [tvar_open_map]
    simp [PType.rename]

lemma TypeMap.ext_var_then (g : TypeMap n m1 m2) :
  g.ext_var = g.then weaken_map id := by
  funext x
  cases m1 with
  | zero => aesop
  | succ _ => 
    cases x using Fin.cases <;> simp [ext_var, TypeMap.then, PType.weaken_var]

lemma TypeMap.ext_var_def (g : TypeMap n m1 m2) :
  g.ext_var = fun x => (g x).weaken_var := by
  rw [TypeMap.ext_var_then]
  simp [TypeMap.then, PType.weaken_var]

lemma TypeMap.weaken_ext_comm (g : TypeMap n m1 m2) :
  g.ext_tvar.compv weaken_map = g.then id weaken_map := by
  funext x
  simp [weaken_map, ext_tvar, compv, TypeMap.then, PType.weaken_tvar]

lemma TypeMap.ext_var_open (g : TypeMap n m1 m2) :
  g.ext_var.then (open_map k) id = g := by
  funext x
  simp [ext_var, TypeMap.then]
  unfold PType.weaken_var
  simp [PType.rename_comp]

def TypeMap.id {n m : Nat} : TypeMap n m m := fun X => PType.tvar X

@[simp]
lemma TypeMap.id_ext_var {n m} : (TypeMap.id (n := n) (m := m)).ext_var = TypeMap.id := by
  funext X
  cases m with
  | zero => cases X.isLt
  | succ => simp [ext_var, id, PType.weaken_var, PType.rename]

@[simp]
lemma TypeMap.id_ext_tvar {n m} : (TypeMap.id (n := n) (m := m)).ext_tvar = TypeMap.id := by
  funext X
  cases X using Fin.cases with
  | H0 => simp [ext_tvar, id, PType.weaken_tvar, PType.rename]
  | Hs X0 => simp [ext_tvar, id, PType.weaken_tvar, PType.rename, weaken_map]
