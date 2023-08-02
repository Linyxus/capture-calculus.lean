import Mathlib.Data.Fin.Basic

import CC.Basic
import CC.CaptureSet
import CC.Type
import CC.Context
import CC.TypeMap
import CC.Typed
import CC.Subcapt
import CC.Subcapt.Basic
import CC.Subtype.Basic
import CC.Subtype.Inversion

namespace CC

theorem Typed.value_typing
  (h : Typed Γ t C T)
  (hval : Value t) :
  T ≠ CType.capt C0 (PType.tvar X) := by
  induction h <;> try (solve | cases hval | aesop)
  case sub =>
    rename_i ht hsub ih
    intro he
    subst_vars
    cases hsub; rename_i hsub
    have h1 := SubtypeP.tvar_inv hsub
    cases h1
    subst_vars
    aesop
