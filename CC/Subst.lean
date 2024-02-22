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
import CC.Subcapt.Rename

namespace CC

inductive SubcaptR : Ctx n m -> Region n -> CaptureSet n -> Prop where
| scr_glob : SubcaptR Γ Region.glob C
| scr_var :
  Subcapt Γ ⟨∅, {x}, false⟩ C ->
  SubcaptR Γ (Region.var x) C

theorem SubcaptR.rename
  (h : SubcaptR Γ r C)
  (σ : VarRename Γ Δ f g) :
  SubcaptR Δ (r.rename f) (C.rename f) := by
  cases h
  case scr_glob =>
    constructor
  case scr_var h =>
    apply scr_var
    have h' := h.rename σ
    exact h'

theorem SubcaptR.weaken_var (h : SubcaptR Γ r C) P p :
  SubcaptR (Ctx.extend_var Γ P p) r.weaken_var C.weaken_var := by
  apply SubcaptR.rename
  exact h
  apply VarRename.weaken_var_map

theorem SubcaptR.weaken_tvar (h : SubcaptR Γ r C) P :
  SubcaptR (Ctx.extend_tvar Γ P) r C := by
  have heq1 : r.rename id = r := by simp [Region.rename_id]
  have heq2 : C.rename id = C := by simp [CaptureSet.rename]
  rw [<- heq1, <- heq2]
  apply SubcaptR.rename
  exact h
  apply VarRename.weaken_tvar_map

theorem SubcaptR.from_bound_var
  (hb : BoundVar Γ x T r) :
  SubcaptR Γ r ⟨∅, {x}, false⟩ := by
  induction hb
  case here r =>
    cases r
    case glob => constructor
    case var =>
      apply scr_var
      apply Subcapt.sc_region
      constructor
  case there_var P p _ ih =>
    have ih' := ih.weaken_var P p
    exact ih'
  case there_tvar P _ ih =>
    have ih' := ih.weaken_tvar P
    exact ih'

def VarSubst (Γ : Ctx n1 m) (Δ : Ctx n2 m) (f : VarMap n1 n2) : Prop :=
  ∀ {x T r}, BoundVar Γ x T r ->
    Typed Δ (Term.var (f x)) {f x} (T.rename f id) ∧
     SubcaptR Δ (r.rename f) ⟨∅, {f x}, false⟩

def TVarSubst (Γ : Ctx n m1) (Δ : Ctx n m2) (g : TypeMap n m1 m2) : Prop :=
  ∀ {X S}, BoundTVar Γ X S -> SubtypeP Δ (g X) (S.tsubst g)

def VarTypeMap (Γ : Ctx n m1) (Δ : Ctx n m2) (g : TypeMap n m1 m2) : Prop :=
  ∀ {x T r}, BoundVar Γ x T r -> BoundVar Δ x (T.tsubst g) r

theorem Typed.var_bound_type :
  BoundVar Γ x T r ->
  Typed Γ (Term.var x) {x} T := by
  intro hb
  cases T
  apply Typed.sub
  · apply Typed.var
    trivial
  · apply Subtype.capt
    apply Subcapt.sc_var
    exact hb
    constructor

def VarSubst.ext_var (σ : VarSubst Γ Δ f) P :
  VarSubst (Ctx.extend_var Γ P p) (Ctx.extend_var Δ (P.rename f id) (p.rename f)) f.ext := by
  intros x T r h
  cases h
  case here =>
    apply And.intro
    · conv =>
        arg 2
        simp [VarMap.ext]
      conv =>
        arg 3
        simp [VarMap.ext]
      rw [<- CType.rename_weaken_comm]
      apply Typed.var_bound_type
      constructor
    · simp
      rw [<- Region.rename_weaken_comm]
      apply SubcaptR.from_bound_var
      constructor
  case there_var h =>
    apply And.intro
    case left =>
      conv =>
        arg 2
        simp [VarMap.ext]
      conv =>
        arg 3
        simp [VarMap.ext]
      rw [<- CType.rename_weaken_comm]
      have ⟨h', _⟩ := σ h
      have h'' := h'.weaken_var (P.rename f id)
      apply h''
    case right =>
      simp [ext_succ]
      rw [<- Region.rename_weaken_comm]
      have ⟨_, h'⟩ := σ h
      have h'' := h'.weaken_var (P.rename f id)
      apply h''

def VarTypeMap.ext_var
  (σ : VarTypeMap Γ Δ g) T :
  VarTypeMap (Ctx.extend_var Γ T r) (Ctx.extend_var Δ (T.tsubst g) r) g.ext_var := by
  intros x T r h
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
  intros X S r h
  cases h
  case there_tvar =>
    rw [CType.tsubst_weaken_tvar_comm]
    constructor
    apply σ
    trivial

def TVarSubst.ext_var
  (δ : TVarSubst Γ Δ g) P :
  TVarSubst (Ctx.extend_var Γ P p) (Ctx.extend_var Δ (P.tsubst g) p) g.ext_var := by
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
  intros X T r h
  cases h
  case there_tvar h =>
    apply And.intro
    · conv =>
        arg 2
        simp [VarMap.ext]
      conv =>
        arg 3
        simp [VarMap.ext]
      rw [<- id_ext]
      rw [<- CType.rename_weaken_tvar_comm]
      have ⟨h', _⟩ := σ h
      have h'' := h'.weaken_tvar (R.rename f id)
      exact h''
    · simp [ext_succ]
      have ⟨_, h'⟩ := σ h
      have h'' := h'.weaken_tvar (R.rename f id)
      exact h''

def VarSubst.open_var {Γ : Ctx n m} {y : Fin n}
  (h : Typed Γ (Term.var y) {y} P)
  (hs : SubcaptR Γ p ⟨∅, {y}, false⟩) :
  VarSubst (Ctx.extend_var Γ P p) Γ (open_map y) := by
  unfold VarSubst
  intros x T r hb
  cases hb
  case here =>
    apply And.intro
    case left =>
      simp
      unfold CType.weaken_var
      simp [CType.rename_comp]
      trivial
    case right =>
      simp
      unfold Region.weaken_var
      simp [Region.rename_comp]
      trivial
  case there_var =>
    apply And.intro
    case left =>
      simp
      unfold CType.weaken_var
      simp [CType.rename_comp]
      apply Typed.var_bound_type; aesop
    case right =>
      simp
      unfold Region.weaken_var; simp [Region.rename_comp]
      apply SubcaptR.from_bound_var; trivial

def TVarRename.open_var (h : Typed Γ (Term.var y) {y} P) :
  TVarRename (Ctx.extend_var Γ P p) Γ (open_map y) id := by
  unfold TVarRename
  intros X S h
  cases h
  rename_i hb
  simp
  unfold PType.weaken_var
  simp [PType.rename_comp]
  trivial
