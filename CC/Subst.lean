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
import CC.Subtype.Rename

namespace CC

def VarSubst (Γ : Ctx n1 m) (Δ : Ctx n2 m) (f : VarMap n1 n2) : Prop :=
  ∀ {x T}, BoundVar Γ x T -> Typed Δ (Term.var (f x)) {f x} (T.rename f id)

def TVarSubst (Γ : Ctx n m1) (Δ : Ctx n m2) (g : TypeMap n m1 m2) : Prop :=
  ∀ {X S}, BoundTVar Γ X S -> SubtypeP Δ (g X) (S.tsubst g)

def VarTypeMap (Γ : Ctx n m1) (Δ : Ctx n m2) (g : TypeMap n m1 m2) : Prop :=
  ∀ {x T}, BoundVar Γ x T -> BoundVar Δ x (T.tsubst g)

theorem Typed.var_bound_type :
  BoundVar Γ x T ->
  Typed Γ (Term.var x) {x} T := by
  intro hb
  cases T
  case capt =>
    apply Typed.sub
    apply Typed.var
    trivial
    apply Subtype.capt
    apply Subcapt.sc_var
    exact hb
    constructor
  case cap =>
    rw [<- CType.at_cap]
    apply Typed.sub
    apply Typed.var
    assumption
    simp [CType.at_cap]
    apply Subtype.cap
    apply Subcapt.sc_nest; assumption
    assumption

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

def VarTypeMap.ext_var 
  (σ : VarTypeMap Γ Δ g) T :
  VarTypeMap (Ctx.extend_var Γ T) (Ctx.extend_var Δ (T.tsubst g)) g.ext_var := by
  intros x T h
  cases h
  case here => 
    rw [CType.tsubst_weaken_var_comm]
    constructor
  case there_var =>
    rw [CType.tsubst_weaken_var_comm]
    constructor
    apply σ
    trivial

def VarTypeMap.ext_tvar
  (σ : VarTypeMap Γ Δ g) S :
  VarTypeMap (Ctx.extend_tvar Γ S) (Ctx.extend_tvar Δ (S.tsubst g)) g.ext_tvar := by
  intros X S h
  cases h
  case there_tvar =>
    rw [CType.tsubst_weaken_tvar_comm]
    constructor
    apply σ
    trivial

def TVarSubst.ext_var
  (δ : TVarSubst Γ Δ g) P :
  TVarSubst (Ctx.extend_var Γ P) (Ctx.extend_var Δ (P.tsubst g)) g.ext_var := by
  intros X S h
  cases h
  case there_var h0 =>
    conv =>
      arg 2
      simp [TypeMap.ext_var]
    rw [PType.tsubst_weaken_var_comm]
    apply SubtypeP.weaken_var
    apply δ
    trivial

def TVarSubst.ext_tvar
  (δ : TVarSubst Γ Δ g) S :
  TVarSubst (Ctx.extend_tvar Γ S) (Ctx.extend_tvar Δ (S.tsubst g)) g.ext_tvar := by
  intros X S h
  cases h
  case here =>
    conv =>
      arg 2
      simp [TypeMap.ext_tvar]
    rw [PType.tsubst_weaken_tvar_comm]
    apply SubtypeP.tvar
    constructor
  case there_tvar =>
    conv =>
      arg 2
      simp [TypeMap.ext_tvar]
    rw [PType.tsubst_weaken_tvar_comm]
    apply SubtypeP.weaken_tvar
    apply δ; trivial

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
