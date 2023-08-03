import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import CC.Basic

namespace CC

structure CaptureSet (n : Nat) where
  elems : Finset (Fin n)

instance : Membership (Fin n) (CaptureSet n) :=
  ⟨fun a s => a ∈ s.1⟩

instance : Singleton (Fin n) (CaptureSet n) :=
  ⟨fun x => ⟨{x}⟩⟩ 

instance : Union (CaptureSet n) :=
  ⟨fun s t => ⟨s.1 ∪ t.1⟩⟩ 

instance : EmptyCollection (CaptureSet n) :=
  ⟨⟨{}⟩⟩

def CaptureSet.rename (C : CaptureSet n1) (f : VarMap n1 n2) : CaptureSet n2 :=
  ⟨C.elems.image f⟩
  
def CaptureSet.weaken_var (C : CaptureSet n) : CaptureSet n.succ :=
  C.rename weaken_map

theorem singleton_val (x : Fin n) :
  ({x} : CaptureSet n).1 = {x} := rfl

@[simp]
theorem rename_singleton (x : Fin n) (f : VarMap n n') :
  CaptureSet.rename {x} f = {f x} := by
  simp [CaptureSet.rename]
  aesop

@[simp]
theorem rename_empty (f : VarMap n n') :
  CaptureSet.rename ∅ f = ∅ := by
  simp [CaptureSet.rename]
  aesop

theorem mem_def {x : Fin n} {C : CaptureSet n} : x ∈ C ↔ x ∈ C.1 := Iff.rfl

theorem mem_rename_of_mem (f : VarMap n1 n2) {C : CaptureSet n1} (h : x ∈ C) : f x ∈ C.rename f := by
  unfold CaptureSet.rename
  simp [mem_def]
  aesop

@[simp]
theorem mem_rename {C : CaptureSet n} :
  y ∈ C.rename f ↔ ∃ x ∈ C, f x = y := by
  simp only [CaptureSet.rename, mem_def]
  aesop

theorem union_def {C1 C2 : CaptureSet n} : C1 ∪ C2 = ⟨C1.1 ∪ C2.1⟩ := rfl

@[simp]
theorem CaptureSet.rename_id : ∀ {C : CaptureSet n},
  C.rename id = C := by
  introv
  simp [CaptureSet.rename]

@[simp]
theorem CaptureSet.rename_id' : ∀ {C : CaptureSet n},
  C.rename (fun x => x) = C := by
  introv
  simp [CaptureSet.rename]

theorem CaptureSet.rename_comp {C : CaptureSet n1} {f1 : VarMap n1 n2} {f2 : VarMap n2 n3} :
  (C.rename f1).rename f2 = C.rename (f2.comp f1) := by
  unfold VarMap.comp
  simp [CaptureSet.rename, Finset.image_image]

theorem CaptureSet.rename_union {C1 C2 : CaptureSet n} :
  (C1 ∪ C2).rename f = C1.rename f ∪ C2.rename f := by
  simp [CaptureSet.rename, union_def, Finset.image_union]

def CaptureSet.open_var (C : CaptureSet n.succ) (z : Fin n) : CaptureSet n :=
  C.rename (open_map z)
  