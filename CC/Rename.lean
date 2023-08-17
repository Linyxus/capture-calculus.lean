import CC.Basic
import CC.Type
import CC.Context
import CC.CaptureSet

namespace CC

def VarRename (Γ : Ctx n1 m1) (Δ : Ctx n2 m2) (f : VarMap n1 n2) (g : VarMap m1 m2) : Prop :=
  ∀ {x D T}, BoundVar Γ x D T -> BoundVar Δ (f x) (D.rename f) (T.rename f g)

def TVarRename (Γ : Ctx n1 m1) (Δ : Ctx n2 m2) (f : VarMap n1 n2) (g : VarMap m1 m2) : Prop :=
  ∀ {X S}, BoundTVar Γ X S -> BoundTVar Δ (g X) (S.rename f g)

def VarRename.weaken_var_map (Γ : Ctx n m) (T : CType n m) :
  VarRename Γ (Ctx.extend_var Γ D T) weaken_map id := by
  intro x D P h
  apply BoundVar.there_var
  trivial

def TVarRename.weaken_var_map (Γ : Ctx n m) (T : CType n m) :
  TVarRename Γ (Ctx.extend_var Γ D T) weaken_map id := by
  intro X P h
  apply BoundTVar.there_var
  trivial

def VarRename.weaken_tvar_map (Γ : Ctx n m) (S : PType n m) :
  VarRename Γ (Ctx.extend_tvar Γ S) id weaken_map := by
  intro x D P h
  apply BoundVar.there_tvar
  simp
  trivial

def TVarRename.weaken_tvar_map (Γ : Ctx n m) (S : PType n m) :
  TVarRename Γ (Ctx.extend_tvar Γ S) id weaken_map := by
  intro X P h
  apply BoundTVar.there_tvar
  trivial

theorem CaptureSet.rename_weaken_var_comp (C : CaptureSet n) :
  C.weaken_var.rename f = C.rename (f.comp weaken_map) := by
  simp [weaken_var]
  simp [CaptureSet.rename_comp]

theorem CaptureSet.weaken_var_rename_comp (C : CaptureSet n) :
  (C.rename f).weaken_var = C.rename (weaken_map.comp f) := by
  simp [weaken_var]
  simp [CaptureSet.rename_comp]

theorem CType.rename_weaken_var_comp (T : CType n m) :
  T.weaken_var.rename f g = T.rename (f.comp weaken_map) g := by
  simp [weaken_var]
  simp [CType.rename_comp]

theorem CType.rename_weaken_tvar_comp (T : CType n m) :
  T.weaken_tvar.rename f g = T.rename f (g.comp weaken_map) := by
  simp [weaken_tvar]
  simp [CType.rename_comp]

theorem SepDegree.rename_weaken_var_comp (S : SepDegree n) :
  S.weaken_var.rename f = S.rename (f.comp weaken_map) := by
  simp [weaken_var]
  simp [SepDegree.rename_comp]

theorem CType.rename_open_comp 
  {n m : Nat} (T : CType n.succ m) 
  {x : Fin n} {f : VarMap n n'} {g : VarMap m m'} :
  (T.open_var x).rename f g = T.rename (f.comp (open_map x)) g := by
  simp [open_var]
  simp [CType.rename_comp]

theorem CType.open_rename_comp {n1 n2 m1 m2} (T : CType n1 m1)
  {x : Fin n2} {f : VarMap n1 n2.succ} {g : VarMap m1 m2} :
  (T.rename f g).open_var x = T.rename ((open_map x).comp f) g := by
  simp [open_var]
  simp [CType.rename_comp]

theorem CType.rename_open_comm {n1 n2 m1 m2} (T : CType n1.succ m1)
  {x : Fin n1} {f : VarMap n1 n2} {g : VarMap m1 m2} :
  (T.open_var x).rename f g = (T.rename f.ext g).open_var (f x) := by
  simp [CType.rename_open_comp]
  simp [comp_open]
  rw [<- CType.open_rename_comp]

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

theorem SepDegree.weaken_var_rename_comp (D : SepDegree n) :
  (D.rename f).weaken_var = D.rename (weaken_map.comp f) := by
  simp [weaken_var]
  simp [SepDegree.rename_comp]

theorem PType.weaken_tvar_rename_comp (S : PType n m) :
  (S.rename f g).weaken_tvar = S.rename f (weaken_map.comp g) := by
  simp [weaken_tvar]
  simp [PType.rename_comp]

theorem PType.weaken_var_rename_comp (S : PType n m) :
  (S.rename f g).weaken_var = S.rename (weaken_map.comp f) g := by
  simp [weaken_var]
  simp [PType.rename_comp]

theorem CType.rename_weaken_comm (T : CType n m) :
  (T.rename f g).weaken_var = T.weaken_var.rename f.ext g := by
  simp [CType.rename_weaken_var_comp]
  rw [<- CType.weaken_var_rename_comp]

theorem PType.rename_weaken_comm (S : PType n m) :
  (S.rename f g).weaken_var = S.weaken_var.rename f.ext g := by
  simp [PType.rename_weaken_var_comp]
  rw [<- PType.weaken_var_rename_comp]

theorem PType.rename_weaken_tvar_comm (S : PType n m) :
  (S.rename f g).weaken_tvar = S.weaken_tvar.rename f g.ext := by
  simp [PType.rename_weaken_tvar_comp]
  rw [<- PType.weaken_tvar_rename_comp]

theorem CType.rename_weaken_tvar_comm (T : CType n m) :
  (T.rename f g).weaken_tvar = T.weaken_tvar.rename f g.ext := by
  simp [CType.rename_weaken_tvar_comp]
  rw [<- CType.weaken_tvar_rename_comp]

theorem CaptureSet.rename_weaken_comm (C : CaptureSet n) :
  (C.rename f).weaken_var = C.weaken_var.rename f.ext := by
  simp [CaptureSet.rename_weaken_var_comp]
  rw [<- CaptureSet.weaken_var_rename_comp]

def VarRename.ext_var 
  {Γ : Ctx n1 m1} {Δ : Ctx n2 m2} 
  (σ : VarRename Γ Δ f g) (T : CType n1 m1) :
  VarRename (Ctx.extend_var Γ D T) (Ctx.extend_var Δ (D.rename f) (T.rename f g)) f.ext g := by
  intro x D P h
  cases h with
  | here =>
    simp [CType.rename_weaken_var_comp, SepDegree.rename_weaken_var_comp]
    rw [<- CType.weaken_var_rename_comp, <- SepDegree.weaken_var_rename_comp]
    simp [VarMap.ext]
    constructor
  | there_var h =>
    simp [CType.rename_weaken_var_comp, SepDegree.rename_weaken_var_comp]
    rw [<- CType.weaken_var_rename_comp, <- SepDegree.weaken_var_rename_comp]
    simp [VarMap.ext]
    constructor
    aesop

def VarRename.ext_tvar {Γ : Ctx n1 m1} {Δ : Ctx n2 m2}
  (σ : VarRename Γ Δ f g) (R : PType n1 m1) :
  VarRename (Ctx.extend_tvar Γ R) (Ctx.extend_tvar Δ (R.rename f g)) f g.ext := by
  intro x D P h
  cases h with
  | there_tvar h =>
    simp [CType.rename_weaken_tvar_comp]
    rw [<- CType.weaken_tvar_rename_comp]
    constructor; aesop

def TVarRename.ext_var {Γ : Ctx n1 m1} {Δ : Ctx n2 m2}
  (δ : TVarRename Γ Δ f g) (T : CType n1 m1) :
  TVarRename (Ctx.extend_var Γ D T) (Ctx.extend_var Δ (D.rename f) (T.rename f g)) f.ext g := by
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

def CType.rename_split (T : CType n m) :
  T.rename f g = (T.rename id g).rename f id := by
  simp [CType.rename_comp]

@[simp]
def weaken1_weaken :
  (weaken_map (n := n)).ext.comp weaken_map = weaken_map.comp weaken_map := by
  funext x
  simp [VarMap.comp, weaken_map, VarMap.ext]

def CType.weaken_var1_weaken_var (T : CType n m) :
  T.weaken_var.weaken_var1 = T.weaken_var.weaken_var := by
  unfold weaken_var1; unfold weaken_var
  simp [CType.rename_comp]

lemma PType.weaken_var1_weaken_var (S : PType n m) :
  S.weaken_var.weaken_var1 = S.weaken_var.weaken_var := by
  unfold weaken_var1; unfold weaken_var
  simp [PType.rename_comp]

lemma SepDegree.weaken_var1_weaken_var (D : SepDegree n) :
  D.weaken_var.weaken_var1 = D.weaken_var.weaken_var := by
  unfold weaken_var1; unfold weaken_var
  simp [SepDegree.rename_comp]

def VarRename.weaken_var1_map (Γ : Ctx n m) (T : CType n m) (P : CType n m) :
  VarRename (Ctx.extend_var Γ D T) (Ctx.extend_var (Ctx.extend_var Γ E P) D.weaken_var T.weaken_var) weaken_map.ext id := by
  intro x F Q h
  cases h with
  | here =>
    conv =>
      arg 2
      simp [VarMap.ext]
    rw [<- CType.weaken_var1_def, <- SepDegree.weaken_var1_def]
    rw [CType.weaken_var1_weaken_var, SepDegree.weaken_var1_weaken_var]
    constructor
  | there_var h0 =>
    conv =>
      arg 2
      simp [VarMap.ext, weaken_map]
    rw [<- CType.weaken_var1_def, <- SepDegree.weaken_var1_def]
    rw [CType.weaken_var1_weaken_var, SepDegree.weaken_var1_weaken_var]
    constructor
    constructor
    trivial

def TVarRename.weaken_var1_map (Γ : Ctx n m) (T : CType n m) (P : CType n m) :
  TVarRename (Ctx.extend_var Γ D T) (Ctx.extend_var (Ctx.extend_var Γ E P) D.weaken_var T.weaken_var) weaken_map.ext id := by
  intro X S h
  cases h with
  | there_var h =>
    simp
    rw [<- PType.weaken_var1_def, PType.weaken_var1_weaken_var]
    constructor; constructor; trivial
