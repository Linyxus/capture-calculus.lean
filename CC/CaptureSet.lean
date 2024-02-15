import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import CC.Basic

namespace CC

structure CaptureSet (n : Nat) where
  elems : Finset (Fin n)
  reachElems: Finset (Fin n)
  hasCap : Bool

instance : Membership (Fin n) (CaptureSet n) :=
  ⟨fun a s => a ∈ s.1⟩

def mem_reach (x : Fin n) (C : CaptureSet n) : Prop :=
  x ∈ C.reachElems

instance : Singleton (Fin n) (CaptureSet n) :=
  ⟨fun x => ⟨{x}, ∅, false⟩⟩

instance : Union (CaptureSet n) :=
  ⟨fun s t => ⟨s.1 ∪ t.1, s.2 ∪ t.2, s.3 ∨ t.3⟩⟩

instance : EmptyCollection (CaptureSet n) :=
  ⟨⟨{}, {}, false⟩⟩

def cap_singleton : CaptureSet n := ⟨{}, {}, true⟩

notation "{cap}" => cap_singleton

def CaptureSet.isUniversal (C : CaptureSet n) : Prop :=
  C.hasCap = true

def CaptureSet.rename (C : CaptureSet n1) (f : VarMap n1 n2) : CaptureSet n2 :=
  ⟨C.elems.image f, C.reachElems.image f, C.hasCap⟩

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
theorem rename_singleton_reach (x : Fin n) (f : VarMap n n') :
  CaptureSet.rename ⟨∅, {x}, false⟩ f = ⟨∅, {f x}, false⟩ := by
  simp [CaptureSet.rename]

@[simp]
theorem rename_singleton_cap :
  CaptureSet.rename {cap} f = {cap} := by
  simp [CaptureSet.rename, cap_singleton]

@[simp]
theorem rename_empty (f : VarMap n n') :
  CaptureSet.rename ∅ f = ∅ := by
  simp [CaptureSet.rename]
  aesop

theorem mem_def {x : Fin n} {C : CaptureSet n} : x ∈ C ↔ x ∈ C.1 := Iff.rfl

theorem mem_reach_def {x : Fin n} {C : CaptureSet n} :
  mem_reach x C ↔ x ∈ C.2 := Iff.rfl

theorem mem_rename_of_mem (f : VarMap n1 n2) {C : CaptureSet n1} (h : x ∈ C) : f x ∈ C.rename f := by
  unfold CaptureSet.rename
  simp [mem_def]
  aesop

instance decidableMem (x : Fin n) (C : CaptureSet n) : Decidable (x ∈ C) :=
  Finset.decidableMem _ _

@[simp]
theorem mem_rename {C : CaptureSet n} :
  y ∈ C.rename f ↔ ∃ x ∈ C, f x = y := by
  simp only [CaptureSet.rename, mem_def]
  aesop

@[simp]
theorem mem_reach_rename {C : CaptureSet n} :
  mem_reach y (C.rename f) ↔ ∃ x, mem_reach x C ∧ f x = y := by
  simp only [CaptureSet.rename, mem_reach_def]
  aesop

theorem CaptureSet.rename_isUniversal {C : CaptureSet n} :
  C.isUniversal -> (C.rename f).isUniversal := by
  intro h
  simp [CaptureSet.isUniversal, CaptureSet.rename] at *
  trivial

theorem CaptureSet.rename_isUniversal' {C : CaptureSet n} :
  (C.rename f).isUniversal -> C.isUniversal := by
  intro h
  simp [CaptureSet.isUniversal, CaptureSet.rename] at *
  trivial

theorem union_def {C1 C2 : CaptureSet n} :
  C1 ∪ C2 = ⟨C1.1 ∪ C2.1, C1.2 ∪ C2.2, C1.3 ∨ C2.3⟩ :=
  rfl

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

lemma CaptureSet.val_eq {C1 C2 : CaptureSet n}
  (h1 : C1.elems = C2.elems)
  (h2 : C1.reachElems = C2.reachElems)
  (h3 : C1.hasCap = C2.hasCap) :
  C1 = C2 :=
  by cases C1; cases C2; aesop

lemma CaptureSet.val_def :
  ({ elems := xs, reachElems := ys, hasCap := u } : CaptureSet n).elems = xs := rfl

lemma CaptureSet.in_union_elems {C1 C2 : CaptureSet n}
  (h : x ∈ (C1 ∪ C2).elems) :
  x ∈ C1.elems ∨ x ∈ C2.elems := by
  cases C1; cases C2
  simp [union_def] at h
  aesop

def CaptureSet.weaken_var1 (C : CaptureSet (Nat.succ n)) : CaptureSet n.succ.succ :=
  C.rename weaken_map.ext
