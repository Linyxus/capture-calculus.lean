import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

import CC.Basic
import CC.Rename

import CC.CaptureSet
import CC.Context
import CC.Term
import CC.Type
import CC.Subtype
import CC.Subtype.Rename
import CC.Typed

namespace CC

def DropBinderFree.rename (h : DropBinderFree C C') :
  DropBinderFree (C.rename f.ext) (C'.rename f) := by
  cases h
  rw [<- CaptureSet.rename_weaken_comm]
  constructor

def DropBinder.rename (h : DropBinder C C') :
  DropBinder (C.rename f.ext) (C'.rename f) := by
  cases h
  case drop_free =>
    apply DropBinder.drop_free
    apply DropBinderFree.rename
    assumption
  case drop =>
    simp [CaptureSet.rename_union]
    rw [<- CaptureSet.rename_weaken_comm]
    apply DropBinder.drop

def Typed.rename {Γ : Ctx n1 m1} (h : Typed Γ t C T)
  {Δ : Ctx n2 m2}
  (σ : VarRename Γ Δ f g)
  (δ : TVarRename Γ Δ f g) :
  Typed Δ (t.rename f g) (C.rename f) (T.rename f g) := by
  induction h generalizing n2 m2 Δ
  case var =>
    simp [Term.rename]
    apply Typed.var
    rename_i hb
    have hb' := σ hb
    simp [CType.rename] at hb'
    exact hb'
  case sub =>
    apply Typed.sub
    aesop
    apply Subtype.rename <;> aesop
  case abs =>
    simp [Term.rename]
    apply Typed.abs
    rename_i ih
    apply ih
    apply σ.ext_var
    apply δ.ext_var
    apply DropBinder.rename
    assumption
  case tabs =>
    simp [Term.rename]
    apply Typed.tabs
    rename_i ih
    apply ih
    apply σ.ext_tvar
    apply δ.ext_tvar
  case app =>
    simp [Term.rename]
    simp [CType.rename_open_comm, CaptureSet.rename_union]
    rename_i ih1 ih2
    have ih1' := ih1 σ δ
    have ih2' := ih2 σ δ
    simp [Term.rename] at ih1' ih2'
    apply Typed.app
    apply ih1'
    apply ih2'
  case tapp => 
    simp [Term.rename]
    simp [CType.rename_open_tvar_comm]
    rename_i ih
    have ih' := ih σ δ
    apply Typed.tapp
    simp [Term.rename] at ih'
    apply ih'
  case box =>
    simp [Term.rename]
    apply Typed.box
    rename_i ih
    apply ih <;> aesop
  case unbox =>
    simp [Term.rename]
    simp [CaptureSet.rename_union]
    apply Typed.unbox
    rename_i ih
    have ih' := ih σ δ
    simp [Term.rename] at ih'
    apply ih'
  case letval1 => 
    simp [Term.rename]
    simp [CaptureSet.rename_union]
    rename_i ih1 ih2
    apply Typed.letval1
    apply ih1 <;> aesop
    apply ih2
    apply VarRename.ext_var; trivial
    apply TVarRename.ext_var; trivial
    subst_vars
    simp [CType.rename_weaken_comm]
    apply DropBinder.rename; trivial
  case letval2 ih1 ih2 => 
    simp [Term.rename]
    apply Typed.letval2
    apply ih1 <;> trivial
    apply Value.rename; trivial
    apply ih2
    apply VarRename.ext_var; trivial
    apply TVarRename.ext_var; trivial
    subst_vars
    simp [CType.rename_weaken_comm]
    apply DropBinderFree.rename; trivial

def Typed.weaken_var (h : Typed Γ t C T) P :
   Typed (Ctx.extend_var Γ P) t.weaken_var C.weaken_var T.weaken_var := by
   apply Typed.rename
   exact h
   apply VarRename.weaken_var_map
   apply TVarRename.weaken_var_map

def Typed.weaken_tvar (h : Typed Γ t C T) P :
   Typed (Ctx.extend_tvar Γ P) t.weaken_tvar C T.weaken_tvar := by
   have heq : C.rename id = C := by simp [CaptureSet.rename]
   rw [<- heq]
   apply Typed.rename
   exact h
   apply VarRename.weaken_tvar_map
   apply TVarRename.weaken_tvar_map

def Typed.weaken_var1 (h : Typed (Ctx.extend_var Γ T0) t C T) P :
  Typed (Ctx.extend_var (Ctx.extend_var Γ P) T0.weaken_var) t.weaken_var1 C.weaken_var1 T.weaken_var1 := by
  apply Typed.rename
  exact h
  apply VarRename.weaken_var1_map
  apply TVarRename.weaken_var1_map

-- def DropBinderFree.weaken_var1
--   (h : DropBinderFree C C') :
--   DropBinderFree C.weaken_var1 C'.weaken_var1 := by
--   unfold CaptureSet.weaken_var1
--   apply DropBinderFree.rename
