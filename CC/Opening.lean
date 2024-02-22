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

def VarTypeMap.open_tvar :
  VarTypeMap (Ctx.extend_tvar Γ S) Γ (tvar_open_map S') := by
  intros x T r h
  cases h with
  | there_tvar h =>
    rw [<- CType.open_tvar_def]
    simp [CType.open_tvar_weaken_tvar_id]
    trivial

def TVarSubst.open_tvar
  (hsub : SubtypeP Γ S' S) :
  TVarSubst (Ctx.extend_tvar Γ S) Γ (tvar_open_map S') := by
  intros X P h
  cases h with
  | here =>
    rw [<- PType.open_tvar_def]
    simp [PType.open_tvar_weaken_tvar_id]
    trivial
  | there_tvar =>
    rw [<- PType.open_tvar_def]
    simp [PType.open_tvar_weaken_tvar_id, tvar_open_map]
    apply SubtypeP.tvar
    trivial
