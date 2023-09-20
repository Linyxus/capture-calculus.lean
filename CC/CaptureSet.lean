import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import CC.BiFin
import CC.Basic

namespace CC

structure CaptureSet (n : Nat) (k : Nat) where
  elems : Finset (BiFin n k)
  rdr : Bool
  cap : Bool

inductive SepDegree (n : Nat) where
| elems : Finset (Fin n) -> SepDegree n
| uniq : SepDegree n

def CaptureSet.rdrSet (C : CaptureSet n k) : CaptureSet n k :=
  { elems := {}, rdr := C.rdr, cap := false }

def CaptureSet.capSet (C : CaptureSet n k) : CaptureSet n k :=
  { elems := {}, rdr := false, cap := C.cap }

def CaptureSet.hasRdr (C : CaptureSet n k) : Prop :=
  C.rdr = true

def CaptureSet.hasCap (C : CaptureSet n k) : Prop :=
  C.cap = true

def SepDegree.isUniq (D : SepDegree n) : Prop :=
  match D with
  | SepDegree.elems _ => false
  | SepDegree.uniq => true

@[simp]
def rdr : CaptureSet n k :=
  { elems := {}, rdr := true, cap := false }

@[simp]
def cap : CaptureSet n k :=
  { elems := {}, rdr := false, cap := true }

instance : Membership (BiFin n k) (CaptureSet n k) :=
  ⟨fun a s => a ∈ s.1⟩

instance : Singleton (BiFin n k) (CaptureSet n k) :=
  ⟨fun x => ⟨{x}, false, false⟩⟩ 

instance : Union (CaptureSet n k) :=
  ⟨fun s t => ⟨s.1 ∪ t.1, s.2 || t.2, s.3 || t.3⟩⟩ 

-- instance : EmptyCollection (CaptureSet n) :=
--   ⟨⟨{}, false, false⟩⟩

-- def SepDegree.mem (a : Fin n) (D : SepDegree n) :=
--   match D with
--   | SepDegree.elems xs => a ∈ xs
--   | SepDegree.uniq => False

-- instance : Membership (Fin n) (SepDegree n) :=
--   ⟨fun a s => s.mem a⟩

-- def SepDegree.singleton (x : Fin n) : SepDegree n :=
--   SepDegree.elems {x}

-- instance : Singleton (Fin n) (SepDegree n) :=
--   ⟨fun x => SepDegree.singleton x⟩

-- -- instance : Union (SepDegree n) :=
-- --   ⟨fun s t => ⟨s.1 ∪ t.1, s.2 || t.2⟩⟩

-- instance : EmptyCollection (SepDegree n) :=
--   ⟨SepDegree.elems {}⟩

-- def CaptureSet.rename (C : CaptureSet n1) (f : VarMap n1 n2) : CaptureSet n2 :=
--   ⟨C.elems.image f, C.rdr, C.cap⟩

-- def SepDegree.rename (C : SepDegree n1) (f : VarMap n1 n2) : SepDegree n2 :=
--   match C with
--   | SepDegree.elems xs => SepDegree.elems (xs.image f)
--   | SepDegree.uniq => SepDegree.uniq
  
-- def CaptureSet.weaken_var (C : CaptureSet n) : CaptureSet n.succ :=
--   C.rename weaken_map

-- def SepDegree.weaken_var (D : SepDegree n) : SepDegree n.succ :=
--   D.rename weaken_map

-- theorem singleton_val (x : Fin n) :
--   ({x} : CaptureSet n).1 = {x} := rfl

-- @[simp]
-- theorem rename_singleton (x : Fin n) (f : VarMap n n') :
--   CaptureSet.rename {x} f = {f x} := by
--   simp [CaptureSet.rename]
--   aesop

-- @[simp]
-- theorem rename_empty (f : VarMap n n') :
--   CaptureSet.rename ∅ f = ∅ := by
--   simp [CaptureSet.rename]
--   aesop

-- @[simp]
-- theorem SepDegree.rename_empty :
--   SepDegree.rename {} f = {} := by
--   simp [SepDegree.rename]
--   aesop

-- theorem mem_def {x : Fin n} {C : CaptureSet n} : x ∈ C ↔ x ∈ C.1 := Iff.rfl

-- theorem singleton_def {x : Fin n} : ({x} : CaptureSet n).elems = {x} := rfl

-- theorem mem_rename_of_mem (f : VarMap n1 n2) {C : CaptureSet n1} (h : x ∈ C) : f x ∈ C.rename f := by
--   unfold CaptureSet.rename
--   simp [mem_def]
--   aesop

-- instance decidableMem (x : Fin n) (C : CaptureSet n) : Decidable (x ∈ C) :=
--   Finset.decidableMem _ _

-- @[simp]
-- theorem mem_rename {C : CaptureSet n} :
--   y ∈ C.rename f ↔ ∃ x ∈ C, f x = y := by
--   simp only [CaptureSet.rename, mem_def]
--   aesop

-- theorem union_def {C1 C2 : CaptureSet n} : 
--   C1 ∪ C2 = ⟨C1.1 ∪ C2.1, C1.2 || C2.2, C1.3 || C2.3⟩ := rfl

-- @[simp]
-- theorem CaptureSet.rename_id : ∀ {C : CaptureSet n},
--   C.rename id = C := by
--   introv
--   simp [CaptureSet.rename]

-- @[simp]
-- theorem SepDegree.rename_id : ∀ {D : SepDegree n},
--   D.rename id = D := by
--   introv
--   cases D <;> simp [SepDegree.rename]

-- @[simp]
-- theorem CaptureSet.rename_id' : ∀ {C : CaptureSet n},
--   C.rename (fun x => x) = C := by
--   introv
--   simp [CaptureSet.rename]

-- theorem CaptureSet.rename_comp {C : CaptureSet n1} {f1 : VarMap n1 n2} {f2 : VarMap n2 n3} :
--   (C.rename f1).rename f2 = C.rename (f2.comp f1) := by
--   unfold VarMap.comp
--   simp [CaptureSet.rename, Finset.image_image]

-- theorem SepDegree.rename_comp {D : SepDegree n1} {f1 : VarMap n1 n2} {f2 : VarMap n2 n3} :
--   (D.rename f1).rename f2 = D.rename (f2.comp f1) := by
--   unfold VarMap.comp
--   cases D <;> simp [SepDegree.rename, Finset.image_image]

-- theorem CaptureSet.rename_union {C1 C2 : CaptureSet n} :
--   (C1 ∪ C2).rename f = C1.rename f ∪ C2.rename f := by
--   simp [CaptureSet.rename, union_def, Finset.image_union]

-- def CaptureSet.open_var (C : CaptureSet n.succ) (z : Fin n) : CaptureSet n :=
--   C.rename (open_map z)

-- lemma CaptureSet.val_eq {C1 C2 : CaptureSet n} 
--   (h1 : C1.elems = C2.elems)
--   (h2 : C1.rdr = C2.rdr)
--   (h3 : C1.cap = C2.cap) :
--   C1 = C2 := 
--   by cases C1; cases C2; aesop

-- lemma CaptureSet.val_def :
--   ({ elems := xs, rdr := b1, cap := b2 } : CaptureSet n).elems = xs := rfl

-- lemma CaptureSet.elems_val_eq {C1 C2 : CaptureSet n}
--   (he : C1 = C2) :
--   C1.elems = C2.elems := by aesop

-- lemma CaptureSet.cap_val_eq {C1 C2 : CaptureSet n}
--   (he : C1 = C2) :
--   C1.cap = C2.cap := by aesop

-- @[simp]
-- lemma CaptureSet.cap_val_def :
--   ({ elems := xs, rdr := b1, cap := b2 } : CaptureSet n).cap = b2 := rfl

-- lemma CaptureSet.in_union_elems {C1 C2 : CaptureSet n}
--   (h : x ∈ (C1 ∪ C2).elems) :
--   x ∈ C1.elems ∨ x ∈ C2.elems := by
--   cases C1; cases C2
--   simp [union_def] at h
--   aesop

-- def CaptureSet.weaken_var1 (C : CaptureSet (Nat.succ n)) : CaptureSet n.succ.succ :=
--   C.rename weaken_map.ext

-- def SepDegree.weaken_var1 (D : SepDegree (Nat.succ n)) : SepDegree n.succ.succ :=
--   D.rename weaken_map.ext

-- lemma SepDegree.weaken_var1_def {D : SepDegree (Nat.succ n)} :
--   D.weaken_var1 = D.rename weaken_map.ext := rfl

-- lemma SepDegree.empty_weaken_var1 :
--   ({} : SepDegree (Nat.succ n)).weaken_var1 = {} := by simp [weaken_var1]

-- lemma SepDegree.empty_weaken_var :
--   ({} : SepDegree n).weaken_var = {} := by simp [weaken_var]

-- @[simp]
-- lemma CaptureSet.rdrSet_rdrSet (C : CaptureSet n) :
--   C.rdrSet.rdrSet = C.rdrSet := by
--   cases C; simp [CaptureSet.rdrSet]

-- @[simp]
-- lemma CaptureSet.mem_singleton
--   {x : Fin n} :
--   x ∈ ({y} : CaptureSet n) ↔ x = y := by
--   simp [mem_def] at *
--   simp [singleton_def] at *

-- lemma CaptureSet.singleton_def' (x : Fin n) :
--   ({x} : CaptureSet n) = { elems := {x}, rdr := false, cap := false } := by
--   rfl

-- lemma CaptureSet.empty_def :
--   (∅ : CaptureSet n) = { elems := ∅, rdr := false, cap := false } := by
--   rfl

-- @[simp]
-- lemma CaptureSet.singleton_rdrSet (x : Fin n) :
--   ({x} : CaptureSet n).rdrSet = ∅ := by
--   rw [CaptureSet.singleton_def', rdrSet]
--   simp [empty_def]

-- @[simp]
-- lemma CaptureSet.empty_rdrSet :
--   ({} : CaptureSet n).rdrSet = ∅ := by
--   simp [empty_def, rdrSet]

-- @[simp]
-- lemma CaptureSet.empty_capSet :
--   ({} : CaptureSet n).capSet = ∅ := by
--   simp [empty_def, capSet]

-- lemma CaptureSet.singleton_eq_empty_absurd :
--   ({x} : CaptureSet n) = { elems := {}, rdr := b1, cap := b2 } → False := by
--   rw [singleton_def']
--   intros he
--   have he1 := CaptureSet.elems_val_eq he
--   rw [val_def] at he1; simp [val_def] at he1

-- -- def SepDegree.as_cset (D : SepDegree n) : CaptureSet n := 
-- --   { elems := D.elems, rdr := false, cap := false }

-- lemma CaptureSet.singleton_hasRdr_absurd {x : Fin n} :
--   ({x} : CaptureSet n).hasRdr → False := by simp [CaptureSet.hasRdr]

-- lemma CaptureSet.singleton_hasCap_absurd {x : Fin n} :
--   ({x} : CaptureSet n).hasCap → False := by simp [CaptureSet.hasCap]

-- lemma cap_hasCap :
--   (cap : CaptureSet n).hasCap := by simp [CaptureSet.hasCap]

-- lemma rdr_hasRdr :
--   (rdr : CaptureSet n).hasRdr := by simp [CaptureSet.hasRdr]
