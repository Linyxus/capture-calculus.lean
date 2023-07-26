import CC.Basic
import CC.Type
import CC.Context

namespace CC

def VarRename (Γ : Ctx n1 m1) (Δ : Ctx n2 m2) (f : VarMap n1 n2) (g : VarMap m1 m2) : Prop :=
  ∀ {x T}, BoundVar Γ x T -> BoundVar Δ (f x) (T.rename f g)

def TVarRename (Γ : Ctx n1 m1) (Δ : Ctx n2 m2) (f : VarMap n1 n2) (g : VarMap m1 m2) : Prop :=
  ∀ {X S}, BoundTVar Γ X S -> BoundTVar Δ (g X) (S.rename f g)

theorem CType.rename_weaken_var_comp (T : CType n m) :
  T.weaken_var.rename f g = T.rename (f.comp weaken_map) g := by
  simp [weaken_var]
  simp [CType.rename_comp]

theorem CType.rename_weaken_tvar_comp (T : CType n m) :
  T.weaken_tvar.rename f g = T.rename f (g.comp weaken_map) := by
  simp [weaken_tvar]
  simp [CType.rename_comp]

theorem PType.rename_weaken_var_comp (S : PType n m) :
  S.weaken_var.rename f g = S.rename (f.comp weaken_map) g := by
  simp [weaken_var]
  simp [PType.rename_comp]

theorem PType.rename_weaken_tvar_comp (S : PType n m) :
  S.weaken_tvar.rename f g = S.rename f (g.comp weaken_map) := by
  simp [weaken_tvar]
  simp [PType.rename_comp]

theorem CType.weaken_var_rename_comp (T : CType n m) :
  (T.rename f g).weaken_var = T.rename (weaken_map.comp f) g := by
  simp [weaken_var]
  simp [CType.rename_comp]

theorem CType.weaken_tvar_rename_comp (T : CType n m) :
  (T.rename f g).weaken_tvar = T.rename f (weaken_map.comp g) := by
  simp [weaken_tvar]
  simp [CType.rename_comp]

theorem PType.weaken_tvar_rename_comp (S : PType n m) :
  (S.rename f g).weaken_tvar = S.rename f (weaken_map.comp g) := by
  simp [weaken_tvar]
  simp [PType.rename_comp]

theorem PType.weaken_var_rename_comp (S : PType n m) :
  (S.rename f g).weaken_var = S.rename (weaken_map.comp f) g := by
  simp [weaken_var]
  simp [PType.rename_comp]

def VarRename.ext_var {Γ : Ctx n1 m1} {Δ : Ctx n2 m2} 
  (σ : VarRename Γ Δ f g) (T : CType n1 m1) :
  VarRename (Ctx.extend_var Γ T) (Ctx.extend_var Δ (T.rename f g)) f.ext g := by
  intro x P h
  cases h with
  | here =>
    simp [CType.rename_weaken_var_comp]
    rw [<- CType.weaken_var_rename_comp]
    simp [VarMap.ext]
    constructor
  | there_var h =>
    simp [CType.rename_weaken_var_comp]
    rw [<- CType.weaken_var_rename_comp]
    simp [VarMap.ext]
    constructor
    aesop

def VarRename.ext_tvar {Γ : Ctx n1 m1} {Δ : Ctx n2 m2}
  (σ : VarRename Γ Δ f g) (R : PType n1 m1) :
  VarRename (Ctx.extend_tvar Γ R) (Ctx.extend_tvar Δ (R.rename f g)) f g.ext := by
  intro x P h
  cases h with
  | there_tvar h =>
    simp [CType.rename_weaken_tvar_comp]
    rw [<- CType.weaken_tvar_rename_comp]
    constructor; aesop

def TVarRename.ext_var {Γ : Ctx n1 m1} {Δ : Ctx n2 m2}
  (δ : TVarRename Γ Δ f g) (T : CType n1 m1) :
  TVarRename (Ctx.extend_var Γ T) (Ctx.extend_var Δ (T.rename f g)) f.ext g := by
  intro X R h
  cases h with
  | there_var h =>
    simp [PType.rename_weaken_var_comp]
    rw [<- PType.weaken_var_rename_comp]
    constructor
    aesop

def TVarRename.ext_tvar {Γ : Ctx n1 m1} {Δ : Ctx n2 m2}
  (δ : TVarRename Γ Δ f g) (R : PType n1 m1) :
  TVarRename (Ctx.extend_tvar Γ R) (Ctx.extend_tvar Δ (R.rename f g)) f g.ext := by
  intro X R h
  cases h with
  | here =>
    simp [PType.rename_weaken_tvar_comp]
    rw [<- PType.weaken_tvar_rename_comp]
    simp [VarMap.ext]
    constructor
  | there_tvar h =>
    simp [PType.rename_weaken_tvar_comp]
    rw [<- PType.weaken_tvar_rename_comp]
    constructor
    aesop
