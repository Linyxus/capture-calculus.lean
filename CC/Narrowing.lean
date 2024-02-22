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
  VarSubst (Ctx.extend_var Γ T r) (Ctx.extend_var Γ T' r) id := by
  unfold VarSubst
  intro x P p hb
  cases x using Fin.cases with
  | H0 =>
    apply And.intro
    case left =>
      simp
      cases hb
      apply Typed.sub
      apply Typed.var_bound_type
      constructor
      apply Subtype.weaken_var
      trivial
    case right =>
      simp
      cases hb
      apply SubcaptR.from_bound_var; constructor
  | Hs x0 =>
    apply And.intro
    case left =>
      simp
      let ⟨P0, r0, he1, he2, hb0⟩ := BoundVar.pred hb
      subst_vars
      apply Typed.var_bound_type
      constructor
      trivial
    case right =>
      simp
      let ⟨P0, r0, he1, he2, hb0⟩ := BoundVar.pred hb
      subst_vars
      apply SubcaptR.from_bound_var; constructor; trivial

def TVarRename.narrowing_var :
  TVarRename (Ctx.extend_var Γ T p) (Ctx.extend_var Γ T' p) id id := by
  unfold TVarRename
  intros X S h
  simp
  cases h
  constructor
  trivial

def VarTypeMap.narrowing_tvar :
  VarTypeMap (Ctx.extend_tvar Γ T) (Ctx.extend_tvar Γ T') TypeMap.id := by
  unfold VarTypeMap
  intros x T r h
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
