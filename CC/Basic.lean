import Mathlib.Data.Fin.Basic
import CC.BiFin

namespace CC

def VarMap (n m : Nat) : Type := Fin n -> Fin m

def VarMap.ext (f : VarMap n m) : VarMap n.succ m.succ := by
  intro i
  cases i using Fin.cases with
  | H0 => exact 0
  | Hs i0 => exact (f i0).succ

def VarMap.comp (f : VarMap n2 n3) (f' : VarMap n1 n2) : VarMap n1 n3 := Function.comp f f'

def BVarMap (n1 k1 n2 k2 : Nat) : Type := BiFin n1 k1 -> BiFin n2 k2

def BVarMap.comp (f : BVarMap n2 k2 n3 k3) (f' : BVarMap n1 k1 n2 k2) : BVarMap n1 k1 n3 k3 := Function.comp f f'

-- def BVarMap.ext (f : BVarMap n1 k1 n2 k2) : BVarMap n1.succ k1 n2.succ k2 := by
--   intro i
--   cases i with
--   | injn i => exact injn i.succ
--   | injk i => exact (f (BiFin.injk i))

def weaken_map : VarMap n n.succ := fun x => x.succ

def weaken_bmap : BVarMap n k n.succ k := fun x =>
  match x with
  | BiFin.injn x => BiFin.injn x.succ
  | BiFin.injk x => BiFin.injk x

def weaken_n_map (k : Nat) : VarMap n (n+k) := fun x => Fin.addNat k x

def open_map (k : Fin n) : VarMap n.succ n := by
  intro i
  cases i using Fin.cases with
  | H0 => exact k
  | Hs i0 => exact i0

def open_bmap (k : Fin n) : BVarMap n.succ k0 n k0 := by
  intro i
  cases i with
  | injn i => 
    cases i using Fin.cases with
    | H0 => exact BiFin.injn k
    | Hs i0 => exact BiFin.injn i0
  | injk i =>
    exact BiFin.injk i

@[simp]
theorem open_map_zero (k : Fin n) :
  open_map k 0 = k := by aesop

@[simp]
theorem open_map_succ :
  open_map k x.succ = x := by aesop

@[simp]
theorem id_ext : VarMap.ext (n := n) id = id := by
  unfold VarMap
  ext x
  cases x using Fin.cases <;> aesop

theorem ext_comp {f1 : VarMap n1 n2} {f2 : VarMap n2 n3} :
  VarMap.ext (f2.comp f1) = f2.ext.comp f1.ext := by
  unfold VarMap
  ext x0
  cases x0 using Fin.cases <;> aesop

@[simp]
theorem comp_id (f : VarMap n1 n2) :
  f.comp id = f := by
  unfold VarMap
  ext x0
  simp [VarMap.comp]

@[simp]
theorem id_comp (f : VarMap n1 n2) :
  VarMap.comp id f = f := by
  unfold VarMap
  ext x0
  simp [VarMap.comp]

@[simp]
theorem ext_comp_weaken (f : VarMap n1 n2) :
  f.ext.comp weaken_map = weaken_map.comp f := by aesop

@[simp]
theorem open_comp_weaken :
  (open_map k).comp weaken_map = id := by
  funext x
  simp [VarMap.comp, weaken_map, open_map]

theorem comp_open (f : VarMap n1 n2) (x : Fin n1) :
  f.comp (open_map x) = (open_map (f x)).comp f.ext := by
  simp [VarMap.comp]
  funext z
  cases z using Fin.cases with
  | H0 =>
    conv =>
      lhs
      simp [open_map]
  | Hs z0 =>
    conv =>
      lhs
      simp [open_map]

@[simp]
theorem ext_zero (f : VarMap n1 n2) :
  f.ext 0 = 0 := by simp [VarMap.ext]
