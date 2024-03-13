import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.PImage
import Mathlib.Data.PFun

import CC.CaptureSet
import CC.Basic
import CC.CaptureSet
import CC.Type
import CC.Type.TypeSubst
import CC.Term
import CC.Context
import CC.Subtype
import CC.Sep

namespace CC

inductive DropBinderFree : CaptureSet n.succ -> CaptureSet n -> Prop where
  | drop : DropBinderFree C.weaken_var C

inductive DropBinder : CaptureSet n.succ -> CaptureSet n -> Prop where
  | drop_free : DropBinderFree C C' -> DropBinder C C'
  | drop : DropBinder (C.weaken_var ∪ {0}) C

inductive Sep' : LetMode -> Ctx n m -> CaptureSet n -> CaptureSet n -> Prop where
| seq : Sep' LetMode.seq Γ C1 C2
| par : Sep Γ C1 C2 -> Sep' LetMode.par Γ C1 C2

inductive LetC : LetMode -> Term n m -> CaptureSet n -> CaptureSet n.succ -> CaptureSet n -> Prop where
  | normal :
    DropBinder Cu Cu' ->
    Sep' M Γ Ct Cu' ->
    LetC M t Ct Cu (Ct ∪ Cu')
  | gc :
    DropBinderFree Cu Cu' ->
    Sep' M Γ Ct Cu' ->
    Value t ->
    LetC M t Ct Cu Cu'

inductive Typed : Ctx n m -> Term n m -> CaptureSet n -> CType n m -> Prop where
| var :
  BoundVar Γ x D (CType.capt C S) ->
  Typed Γ (Term.var x) {x} (CType.capt {x} S)
| sub :
  Typed Γ t C T ->
  Subtype Γ T T' ->
  Typed Γ t C T'
| abs :
  Typed (Ctx.extend_var Γ (SepDegree.elems D) T) t C U ->
  DropBinder C C' ->
  Typed Γ (Term.abs D T t) C' (CType.capt C' (PType.arr D T U))
| tabs :
  Typed (Ctx.extend_tvar Γ S) t C T ->
  Typed Γ (Term.tabs S t) C (CType.capt C (PType.tarr S T))
| app :
  Typed Γ (Term.var x) Cx (CType.capt C (PType.arr D T U)) ->
  Typed Γ (Term.var y) Cy T ->
  Sep Γ {y} { elems := D, cap := false, rdr := false } ->
  Typed Γ (Term.app x y) (Cx ∪ Cy) (U.open_var y)
| tapp :
  Typed Γ (Term.var x) Cx (CType.capt C (PType.tarr S T)) ->
  Typed Γ (Term.tapp x S) Cx (T.open_tvar S)
| box :
  Typed Γ (Term.var x) Cx (CType.capt C S) ->
  Typed Γ (Term.box x) {} (CType.capt {} (PType.boxed (CType.capt C S)))
| unbox :
  Typed Γ (Term.var x) Cx (CType.capt C0 (PType.boxed (CType.capt C S))) ->
  Typed Γ (Term.unbox C x) (C ∪ {x}) (CType.capt C S)
| letval :
  Typed Γ t Ct T ->
  Typed (Ctx.extend_var Γ {} T) u Cu U ->
  U = U'.weaken_var ->
  LetC M t Ct Cu Cu' ->
  Typed Γ (Term.letval M t u) Cu' U'
| letvar :
  Typed Γ (Term.var y) Cy (CType.capt {} S) ->
  Typed (Ctx.extend_var Γ D (CType.capt { elems := {}, rdr := false, cap := true } (PType.ref S))) t Ct U ->
  U = U'.weaken_var ->
  DropBinder Ct Ct' ->
  Typed Γ (Term.letvar D y t) (Ct' ∪ {y}) U'
| reader :
  Typed Γ (Term.var x) Cx (CType.capt C (PType.ref S)) ->
  Typed Γ (Term.reader x) {x} (CType.capt {x} (PType.reader S))
| read :
  Typed Γ (Term.var x) Cx (CType.capt C (PType.reader S)) ->
  Typed Γ (Term.read x) {x} (CType.capt {} S)
| write :
  Typed Γ (Term.var x) Cx (CType.capt C (PType.ref S)) ->
  Typed Γ (Term.var y) Cy (CType.capt {} S) ->
  Typed Γ (Term.write x y) (Cx ∪ Cy) (CType.capt {} S)

-- The following provides a function that computes the capture set defined by DropBinder.
-- They are currently unused, therefore commented and unported.

-- def lower_var : Fin (Nat.succ n) →. Fin n :=
--   fun x =>
--     { Dom := x ≠ 0, 
--       get := fun h => x.pred h }

-- instance : (x : Fin (Nat.succ n)) → Decidable (lower_var x).Dom := by
--   intro x
--   unfold lower_var
--   simp
--   apply instDecidableNot

-- def CaptureSet.lower (C : CaptureSet n.succ) : CaptureSet n := ⟨Finset.pimage lower_var C.elems⟩

-- theorem CaptureSet.lower_drop_binder_notin
--   {C : CaptureSet (Nat.succ n)}
--   (h : 0 ∉ C) :
--   C.lower.weaken_var = C := by
--   apply CaptureSet.val_eq
--   ext a0
--   constructor
--   · intros h
--     unfold weaken_var at h; unfold rename at h; unfold lower at h
--     repeat rw [val_def] at h
--     rw [Finset.mem_image] at h
--     let ⟨a1, h1, he1⟩ := h; clear h
--     rw [Finset.mem_pimage] at h1
--     let ⟨a2, h2, he2⟩ := h1; clear h1
--     simp [lower_var] at he2
--     let ⟨he2, he3⟩ := he2
--     simp [weaken_map] at he1
--     aesop
--   · intros h
--     simp [weaken_var, lower, rename, weaken_map, lower_var]
--     cases a0 using Fin.cases with
--     | H0 =>
--       rename_i he
--       exfalso
--       apply he
--       simp [mem_def]; trivial
--     | Hs az =>
--       apply Exists.intro az
--       apply And.intro
--       · rw [Finset.mem_pimage]
--         simp
--         apply Exists.intro az.succ
--         constructor; trivial
--         have h0 : az.succ ≠ 0 := by
--           intros h0
--           cases h0
--         aesop
--       · simp

-- theorem CaptureSet.lower_drop_binder_in
--   {C : CaptureSet (Nat.succ n)}
--   (h : 0 ∈ C) :
--   C.lower.weaken_var ∪ {0} = C := by
--   apply CaptureSet.val_eq
--   ext a0
--   constructor
--   · intros h
--     have h1 := in_union_elems h
--     cases h1
--     · rename_i h
--       unfold weaken_var at h; unfold rename at h; unfold lower at h
--       repeat rw [val_def] at h
--       rw [Finset.mem_image] at h
--       let ⟨a1, h1, he1⟩ := h; clear h
--       rw [Finset.mem_pimage] at h1
--       let ⟨a2, h2, he2⟩ := h1; clear h1
--       simp [lower_var] at he2
--       let ⟨he2, he3⟩ := he2
--       simp [weaken_map] at he1
--       aesop
--     · rename_i h0 h
--       simp [singleton_val] at h
--       aesop
--   · intros h
--     simp [union_def]
--     cases a0 using Fin.cases with
--     | H0 =>
--       apply Or.inr
--       simp [singleton_val]
--     | Hs az =>
--       apply Or.inl
--       simp [weaken_var, lower, rename, weaken_map, lower_var]
--       rw [Finset.mem_pimage]
--       simp
--       apply Exists.intro az.succ
--       constructor; trivial
--       have h0 : az.succ ≠ 0 := by
--         intros h0
--         cases h0
--       aesop

-- theorem CaptureSet.lower_drop_binder
--   {C : CaptureSet (Nat.succ n)} [he : Decidable (0 ∈ C)] :
--   DropBinder C C.lower := by
--   cases he with
--   | isFalse he =>
--     have h0 := CaptureSet.lower_drop_binder_notin he
--     conv =>
--       arg 1
--       rw [<- h0]
--     apply DropBinder.drop_free
--     constructor
--   | isTrue he =>
--     have h0 := CaptureSet.lower_drop_binder_in he
--     conv =>
--       arg 1
--       rw [<- h0]
--     apply DropBinder.drop
