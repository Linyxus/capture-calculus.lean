import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

import CC.Basic
import CC.Rename

import CC.CaptureSet
import CC.Context
import CC.EvalContext
import CC.Term
import CC.Term.TypeSubst
import CC.Type
import CC.Reduction

namespace CC

inductive Match : CType n1 m1 -> CType n2 m2 -> Prop where
| same :
  Match T T
| weaken :
  Match T.weaken_var T

theorem preservation :
  TypedState st1 T1 ->
  Reduce st1 st2 ->
  ∃ T2, TypedState st2 T2 ∧ Match T1 T2 := by
  intro ht hr
  induction hr
  case red_app hl =>
    cases ht; rename_i hs hv
    sorry
