import CC.Basic
import CC.Type
import CC.Context
import CC.TypeMap

namespace CC

def PType.tsubst (S : PType n m1) (σ : TypeMap n m1 m2) : PType n m2 :=
  match S with
  | PType.tvar X => σ X
  | PType.top => PType.top
  | PType.arr (CType.capt C1 S1) (CType.capt C2 S2) =>
    PType.arr (CType.capt C1 (S1.tsubst σ)) (CType.capt C2 (S2.tsubst σ.ext_var))
  | PType.tarr S1 (CType.capt C2 S2) =>
    PType.tarr (S1.tsubst σ) (CType.capt C2 (S2.tsubst σ.ext_tvar))
  | PType.boxed (CType.capt C1 S1) =>
    PType.boxed (CType.capt C1 (S1.tsubst σ))

def CType.tsubst (T : CType n m1) (σ : TypeMap n m1 m2) : CType n m2 :=
  match T with
  | CType.capt C S => CType.capt C (S.tsubst σ)

def CType.open_tvar (T : CType n m.succ) (R : PType n m) : CType n m :=
  T.tsubst (tvar_open_map R)

def PType.open_tvar (S : PType n m.succ) (R : PType n m) : PType n m :=
  S.tsubst (tvar_open_map R)

theorem PType.rename_tsubst (T : PType n1 m1)
  {σ : TypeMap n1 m1 m2} {f : VarMap n1 n2} {g : VarMap m2 m3} :
  (T.tsubst σ).rename f g = (T.rename f id).tsubst (σ.then f g) :=
  match T with
  | PType.tvar X => by
    simp [tsubst, rename, TypeMap.then]
  | PType.top => by
    simp [tsubst, rename, TypeMap.then]
  | PType.arr (CType.capt C1 S1) (CType.capt C2 S2) => by
    have ih1 := PType.rename_tsubst S1 (σ := σ) (f := f) (g := g)
    have ih2 := PType.rename_tsubst S2 (σ := σ.ext_var) (f := f.ext) (g := g)
    simp [rename, tsubst, ih1]
    rw [<- TypeMap.ext_var_then_comm]
    simp [ih2]
  | PType.tarr S1 (CType.capt C2 S2) => by
    have ih1 := PType.rename_tsubst S1 (σ := σ) (f := f) (g := g)
    have ih2 := PType.rename_tsubst S2 (σ := σ.ext_tvar) (f := f) (g := g.ext)
    simp [rename, tsubst, ih1]
    rw [<- TypeMap.ext_tvar_then_comm]
    simp [ih2]
  | PType.boxed (CType.capt C1 S1) => by
    have ih1 := PType.rename_tsubst S1 (σ := σ) (f := f) (g := g)
    simp [rename, tsubst, ih1]

theorem CType.rename_tsubst (T : CType n1 m1)
  {σ : TypeMap n1 m1 m2} {f : VarMap n1 n2} {g : VarMap m2 m3} :
  (T.tsubst σ).rename f g = (T.rename f id).tsubst (σ.then f g) := by
  cases T
  simp [rename, tsubst, PType.rename_tsubst]

theorem PType.tsubst_rename (T : PType n1 m1)
  {f : VarMap n1 n2} {g : VarMap m1 m2} {σ : TypeMap n2 m2 m3} :
  (T.rename f g).tsubst σ = (T.rename f id).tsubst (σ.compv g) :=
  match T with
  | PType.tvar X => by
    simp [tsubst, rename, TypeMap.compv]
  | PType.top => by
    simp [tsubst, rename, TypeMap.compv]
  | PType.arr (CType.capt C1 S1) (CType.capt C2 S2) => by
    have ih1 := PType.tsubst_rename S1 (f := f) (g := g) (σ := σ)
    have ih2 := PType.tsubst_rename S2 (f := f.ext) (g := g) (σ := σ.ext_var)
    simp [rename, tsubst, ih1]
    simp [TypeMap.compv_ext_var_comm]
    aesop
  | PType.tarr S1 (CType.capt C2 S2) => by
    have ih1 := PType.tsubst_rename S1 (f := f) (g := g) (σ := σ)
    have ih2 := PType.tsubst_rename S2 (f := f) (g := g.ext) (σ := σ.ext_tvar)
    simp [rename, tsubst, ih1]
    simp [TypeMap.compv_ext_tvar_comm]
    aesop
  | PType.boxed (CType.capt C1 S1) => by
    have ih1 := PType.tsubst_rename S1 (f := f) (g := g) (σ := σ)
    simp [rename, tsubst, ih1]

theorem CType.tsubst_rename (T : CType n1 m1)
  {f : VarMap n1 n2} {g : VarMap m1 m2} {σ : TypeMap n2 m2 m3} :
  (T.rename f g).tsubst σ = (T.rename f id).tsubst (σ.compv g) := by
  cases T
  simp [rename, tsubst]
  rw [PType.tsubst_rename]

theorem CType.rename_open_tvar_comm (T : CType n1 m1.succ)
  {R : PType n1 m1} {f : VarMap n1 n2} {g : VarMap m1 m2} :
  (T.open_tvar R).rename f g = (T.rename f g.ext).open_tvar (R.rename f g) := by
  unfold CType.open_tvar
  simp [CType.rename_tsubst]
  rw [tvar_open_map_rename_comm]
  rw [<- CType.tsubst_rename]

@[simp]
lemma tsubst_arr :
  (PType.arr T U).tsubst f = PType.arr (T.tsubst f) (U.tsubst f.ext_var) := by
  cases T; cases U
  simp [PType.tsubst]
  simp [CType.tsubst]

@[simp]
lemma tsubst_tarr :
  (PType.tarr T U).tsubst f = PType.tarr (T.tsubst f) (U.tsubst f.ext_tvar) := by
  cases U
  simp [PType.tsubst]
  simp [CType.tsubst]

@[simp] 
lemma tsubst_boxed :
  (PType.boxed T).tsubst f = PType.boxed (T.tsubst f) := by
  cases T
  simp [PType.tsubst]
  simp [CType.tsubst]

lemma CType.tsubst_weaken_var_comm (T : CType n m) :
  T.weaken_var.tsubst g.ext_var = (T.tsubst g).weaken_var := by
  rw [TypeMap.ext_var_then]
  unfold CType.weaken_var
  rw [<- CType.rename_tsubst]

lemma PType.tsubst_weaken_var_comm (T : PType n m) :
  T.weaken_var.tsubst g.ext_var = (T.tsubst g).weaken_var := by
  rw [TypeMap.ext_var_then]
  unfold PType.weaken_var
  rw [<- PType.rename_tsubst]

lemma CType.tsubst_weaken_tvar_comm (S : CType n m) :
  S.weaken_tvar.tsubst g.ext_tvar = (S.tsubst g).weaken_tvar := by
  unfold CType.weaken_tvar
  rw [CType.tsubst_rename]
  rw [TypeMap.weaken_ext_comm]
  rw [<- CType.rename_tsubst]

lemma PType.tsubst_weaken_tvar_comm (S : PType n m) :
  S.weaken_tvar.tsubst g.ext_tvar = (S.tsubst g).weaken_tvar := by
  unfold PType.weaken_tvar
  rw [PType.tsubst_rename]
  rw [TypeMap.weaken_ext_comm]
  rw [<- PType.rename_tsubst]