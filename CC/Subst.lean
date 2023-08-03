import Mathlib.Data.Fin.Basic
import CC.Basic
import CC.CaptureSet
import CC.Type
import CC.Type.TypeSubst
import CC.Context
import CC.TypeMap
import CC.Typed
import CC.Subtype
import CC.Term
import CC.Typed.Rename

namespace CC

def VarSubst (Γ : Ctx n1 m) (Δ : Ctx n2 m) (f : VarMap n1 n2) : Prop :=
  ∀ {x T}, BoundVar Γ x T -> Typed Δ (Term.var (f x)) {f x} (T.rename f id)

def TVarSubst (Γ : Ctx n m1) (Δ : Ctx n m2) (g : TypeMap n m1 m2) : Prop :=
  ∀ {X S}, BoundTVar Γ X S -> SubtypeP Δ (g X) (S.tsubst g)

theorem Typed.var_bound_type :
  BoundVar Γ x T ->
  Typed Γ (Term.var x) {x} T := by
  intro hb
  cases T
  apply Typed.sub
  apply Typed.var
  trivial
  apply Subtype.capt
  apply Subcapt.sc_var
  exact hb
  constructor

def VarSubst.ext_var (σ : VarSubst Γ Δ f) P :
  VarSubst (Ctx.extend_var Γ P) (Ctx.extend_var Δ (P.rename f id)) f.ext := by
  intros x T h
  cases h
  case here =>
    conv =>
      arg 2
      simp [VarMap.ext]
    conv =>
      arg 3
      simp [VarMap.ext]
    rw [<- CType.rename_weaken_comm]
    apply Typed.var_bound_type
    constructor
  case there_var h =>
    conv =>
      arg 2
      simp [VarMap.ext]
    conv =>
      arg 3
      simp [VarMap.ext]
    rw [<- CType.rename_weaken_comm]
    have h' := σ h
    have h'' := h'.weaken_var (P.rename f id)
    exact h''

def VarSubst.ext_tvar (σ : VarSubst Γ Δ f) R :
  VarSubst (Ctx.extend_tvar Γ R) (Ctx.extend_tvar Δ (R.rename f id)) f := by
  intros X T h
  cases h
  case there_tvar h =>
    conv =>
      arg 2
      simp [VarMap.ext]
    conv =>
      arg 3
      simp [VarMap.ext]
    rw [<- id_ext]
    rw [<- CType.rename_weaken_tvar_comm]
    have h' := σ h
    have h'' := h'.weaken_tvar (R.rename f id)
    exact h''

def VarSubst.open_var {Γ : Ctx n m} {y : Fin n} (h : Typed Γ (Term.var y) {y} P) :
  VarSubst (Ctx.extend_var Γ P) Γ (open_map y) := by
  unfold VarSubst
  intros x T hb
  cases hb
  case here =>
    simp
    unfold CType.weaken_var
    simp [CType.rename_comp]
    trivial
  case there_var =>
    simp
    unfold CType.weaken_var
    simp [CType.rename_comp]
    apply Typed.var_bound_type; aesop

def TVarRename.open_var (h : Typed Γ (Term.var y) {y} P) :
  TVarRename (Ctx.extend_var Γ P) Γ (open_map y) id := by
  unfold TVarRename
  intros X S h
  cases h
  rename_i hb
  simp
  unfold PType.weaken_var
  simp [PType.rename_comp]
  trivial
