import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

import CC.Basic
import CC.Rename

import CC.CaptureSet
import CC.Context
import CC.Type
import CC.Subcapt
import CC.Subcapt.Basic
import CC.Subcapt.Rename
import CC.Subtype
import CC.Subtype.Rename
import CC.Subtype.Basic
import CC.Subst
import CC.TypeMap
import CC.Type.TypeSubst

namespace CC

def VarSubst.narrowing_var
  (h : Subtype Γ T' T) :
  VarSubst (Ctx.extend_var Γ T) (Ctx.extend_var Γ T') id := by
  unfold VarSubst
  intro x P hb
  cases x using Fin.cases with
  | H0 =>
    simp
    cases hb
    apply Typed.sub
    apply Typed.var_bound_type
    constructor
    apply Subtype.weaken_var
    trivial
  | Hs x0 =>
    simp
    let ⟨P0, he, hb0⟩ := BoundVar.pred hb
    subst_vars
    apply Typed.var_bound_type
    constructor
    trivial

def TVarRename.narrowing_var :
  TVarRename (Ctx.extend_var Γ T) (Ctx.extend_var Γ T') id id := by
  unfold TVarRename
  intros X S h
  simp
  cases h
  constructor
  trivial

def VarTypeMap.narrowing_tvar :
  VarTypeMap (Ctx.extend_tvar Γ T) (Ctx.extend_tvar Γ T') TypeMap.id := by
  unfold VarTypeMap
  intros x T h
  cases h
  simp [CType.tsubst_id]
  constructor; trivial

def TVarSubst.narrowing_tvar (h : SubtypeP Γ T' T) :
  TVarSubst (Ctx.extend_tvar Γ T) (Ctx.extend_tvar Γ T') TypeMap.id := by
  unfold TVarSubst
  intros X S h
  cases h with
  | here =>
    simp [PType.tsubst_id]
    simp [TypeMap.id]
    apply SubtypeP.trans
    apply SubtypeP.tvar
    constructor
    apply SubtypeP.weaken_tvar; trivial
  | there_tvar hb =>
    simp [PType.tsubst_id]
    simp [TypeMap.id]
    apply SubtypeP.tvar
    constructor; trivial
