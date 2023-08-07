import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

import CC.Basic
import CC.Rename

import CC.CaptureSet
import CC.Context
import CC.Type
import CC.Term.TypeSubst
import CC.Subcapt
import CC.Subcapt.Basic
import CC.Subcapt.Rename
import CC.Subtype
import CC.Subtype.Rename
import CC.Subtype.Basic
import CC.Subst
import CC.TypeMap
import CC.Type.TypeSubst
import CC.Typed.TypeSubst
import CC.Opening

namespace CC

def Typed.open_tvar
  (hsub : SubtypeP Γ S' S)
  (h0 : Typed (Ctx.extend_tvar Γ S) t Ct T) :
  Typed Γ (t.open_tvar S') Ct (T.open_tvar S') := by
  unfold Term.open_tvar; unfold CType.open_tvar
  apply Typed.tsubst h0
  apply VarTypeMap.open_tvar
  apply TVarSubst.open_tvar; trivial
