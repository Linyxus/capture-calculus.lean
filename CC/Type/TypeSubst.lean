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
  | PType.arr CType.cap (CType.capt C2 S2) =>
    PType.arr CType.cap (CType.capt C2 (S2.tsubst σ.ext_var))
  | PType.arr (CType.capt C1 S1) CType.cap =>
    PType.arr (CType.capt C1 (S1.tsubst σ)) CType.cap
  | PType.arr CType.cap CType.cap =>
    PType.arr CType.cap CType.cap
  | PType.tarr S1 (CType.capt C2 S2) =>
    PType.tarr (S1.tsubst σ) (CType.capt C2 (S2.tsubst σ.ext_tvar))
  | PType.tarr S1 CType.cap =>
    PType.tarr (S1.tsubst σ) CType.cap
  | PType.boxed (CType.capt C1 S1) =>
    PType.boxed (CType.capt C1 (S1.tsubst σ))
  | PType.boxed CType.cap =>
    PType.boxed CType.cap

def CType.tsubst (T : CType n m1) (σ : TypeMap n m1 m2) : CType n m2 :=
  match T with
  | CType.capt C S => CType.capt C (S.tsubst σ)
  | CType.cap => CType.cap

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
  | PType.arr CType.cap (CType.capt C2 S2) => by
    have ih2 := PType.rename_tsubst S2 (σ := σ.ext_var) (f := f.ext) (g := g)
    simp [rename, tsubst, CType.rename]
    rw [<- TypeMap.ext_var_then_comm]
    simp [ih2]
  | PType.arr (CType.capt C1 S1) CType.cap => by
    have ih1 := PType.rename_tsubst S1 (σ := σ) (f := f) (g := g)
    simp [rename, tsubst, ih1, CType.rename]
  | PType.arr CType.cap CType.cap => by
    simp [rename, tsubst, CType.rename]
  | PType.tarr S1 (CType.capt C2 S2) => by
    have ih1 := PType.rename_tsubst S1 (σ := σ) (f := f) (g := g)
    have ih2 := PType.rename_tsubst S2 (σ := σ.ext_tvar) (f := f) (g := g.ext)
    simp [rename, tsubst, ih1]
    rw [<- TypeMap.ext_tvar_then_comm]
    simp [ih2]
  | PType.tarr S1 CType.cap => by
    have ih1 := PType.rename_tsubst S1 (σ := σ) (f := f) (g := g)
    simp [rename, tsubst, ih1, CType.rename]
  | PType.boxed (CType.capt C1 S1) => by
    have ih1 := PType.rename_tsubst S1 (σ := σ) (f := f) (g := g)
    simp [rename, tsubst, ih1]
  | PType.boxed CType.cap => by
    simp [rename, tsubst, CType.rename]

theorem CType.rename_tsubst (T : CType n1 m1)
  {σ : TypeMap n1 m1 m2} {f : VarMap n1 n2} {g : VarMap m2 m3} :
  (T.tsubst σ).rename f g = (T.rename f id).tsubst (σ.then f g) := by
  cases T <;> simp [rename, tsubst, PType.rename_tsubst]

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
  | PType.arr CType.cap (CType.capt C2 S2) => by
    have ih2 := PType.tsubst_rename S2 (f := f.ext) (g := g) (σ := σ.ext_var)
    simp [rename, tsubst, CType.rename]
    simp [TypeMap.compv_ext_var_comm]
    aesop
  | PType.arr (CType.capt C1 S1) CType.cap => by
    have ih1 := PType.tsubst_rename S1 (f := f) (g := g) (σ := σ)
    simp [rename, tsubst, CType.rename]
    simp [TypeMap.compv_ext_var_comm]
    aesop
  | PType.arr CType.cap CType.cap => by simp [rename, tsubst, CType.rename]
  | PType.tarr S1 (CType.capt C2 S2) => by
    have ih1 := PType.tsubst_rename S1 (f := f) (g := g) (σ := σ)
    have ih2 := PType.tsubst_rename S2 (f := f) (g := g.ext) (σ := σ.ext_tvar)
    simp [rename, tsubst, ih1]
    simp [TypeMap.compv_ext_tvar_comm]
    aesop
  | PType.tarr S1 CType.cap => by
    have ih1 := PType.tsubst_rename S1 (f := f) (g := g) (σ := σ)
    simp [rename, tsubst, CType.rename]
    simp [TypeMap.compv_ext_tvar_comm]
    aesop
  | PType.boxed (CType.capt C1 S1) => by
    have ih1 := PType.tsubst_rename S1 (f := f) (g := g) (σ := σ)
    simp [rename, tsubst, ih1]
  | PType.boxed CType.cap => by
    simp [rename, tsubst, CType.rename]

theorem CType.tsubst_rename (T : CType n1 m1)
  {f : VarMap n1 n2} {g : VarMap m1 m2} {σ : TypeMap n2 m2 m3} :
  (T.rename f g).tsubst σ = (T.rename f id).tsubst (σ.compv g) := by
  cases T <;> simp [rename, tsubst]
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
  cases T <;> cases U <;> simp [PType.tsubst] <;> simp [CType.tsubst]

@[simp]
lemma tsubst_tarr :
  (PType.tarr T U).tsubst f = PType.tarr (T.tsubst f) (U.tsubst f.ext_tvar) := by
  cases U <;> simp [PType.tsubst] <;> simp [CType.tsubst]

@[simp] 
lemma tsubst_boxed :
  (PType.boxed T).tsubst f = PType.boxed (T.tsubst f) := by
  cases T <;> simp [PType.tsubst] <;> simp [CType.tsubst]

@[simp]
lemma tsubst_capt :
  (CType.capt C S).tsubst g = CType.capt C (S.tsubst g) := by aesop

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

lemma CType.tsubst_open_var_comm {n m : Nat} (T : CType n.succ m1) {y : Fin n} {g : TypeMap n m1 m2} :
  (T.open_var y).tsubst g = (T.tsubst g.ext_var).open_var y := by
  unfold CType.open_var
  rw [rename_tsubst]
  rw [TypeMap.ext_var_open]

lemma TypeMap.ext_var_comp (g2 : TypeMap n m2 m3) (g1 : TypeMap n m1 m2) :
  (g1.map (fun P => P.tsubst g2)).ext_var = g1.ext_var.map (fun P => P.tsubst g2.ext_var) := by
  funext x
  cases m1 with
  | zero => cases x.isLt
  | succ m1 =>
    simp [ext_var, TypeMap.map]
    rw [<- ext_var_def]
    simp [PType.tsubst_weaken_var_comm]

lemma PType.tsubst_id (P : PType n m1) :
  P.tsubst TypeMap.id = P :=
  match P with
  | PType.tvar X => by simp [tsubst, TypeMap.id]
  | PType.top => by simp [tsubst]
  | PType.arr (CType.capt C1 S1) (CType.capt C2 S2) => by
    have ih1 := PType.tsubst_id S1
    have ih2 := PType.tsubst_id S2
    simp [tsubst, ih1, ih2]
  | PType.arr CType.cap (CType.capt C2 S2) => by
    have ih2 := PType.tsubst_id S2
    simp [tsubst, CType.tsubst, ih2]
  | PType.arr (CType.capt C1 S1) CType.cap => by
    have ih1 := PType.tsubst_id S1
    simp [tsubst, ih1, CType.tsubst]
  | PType.arr CType.cap CType.cap => by simp [tsubst, CType.tsubst]
  | PType.tarr S1 (CType.capt C2 S2) => by
    have ih1 := PType.tsubst_id S1
    have ih2 := PType.tsubst_id S2
    simp [tsubst, ih1, ih2]
  | PType.tarr S1 CType.cap => by
    have ih1 := PType.tsubst_id S1
    simp [tsubst, ih1, CType.tsubst]
  | PType.boxed (CType.capt C S) => by
    have ih := PType.tsubst_id S
    simp [tsubst, ih]
  | PType.boxed CType.cap => by
    simp [tsubst, CType.tsubst]

lemma CType.tsubst_id (T : CType n m1) :
  T.tsubst TypeMap.id = T := by
  cases T <;> simp [tsubst]
  simp [PType.tsubst_id]

lemma TypeMap.open_tvar_comp_weaken_tvar :
  (tvar_open_map R).compv weaken_map = TypeMap.id := by
  funext X
  simp [compv, weaken_map, tvar_open_map, TypeMap.id]

lemma PType.open_tvar_weaken_tvar_id (P : PType n m) :
  P.weaken_tvar.open_tvar R = P := by
  simp [open_tvar, weaken_tvar]
  simp [tsubst_rename]
  rw [TypeMap.open_tvar_comp_weaken_tvar]
  simp [PType.tsubst_id]

lemma CType.open_tvar_weaken_tvar_id (T : CType n m) :
  T.weaken_tvar.open_tvar R = T := by
  simp [open_tvar, weaken_tvar]
  simp [tsubst_rename]
  rw [TypeMap.open_tvar_comp_weaken_tvar]
  simp [CType.tsubst_id]

lemma TypeMap.ext_tvar_comp (g1 : TypeMap n m1 m2) (g2 : TypeMap n m2 m3) :
  (g1.map (fun P => P.tsubst g2)).ext_tvar = g1.ext_tvar.map (fun P => P.tsubst g2.ext_tvar) := by
  funext X
  cases X using Fin.cases with
  | H0 =>
    conv =>
      lhs
      simp [ext_tvar]
  | Hs x0 => 
    conv =>
      lhs
      simp [ext_tvar]
    simp [map]
    conv =>
      rhs
      arg 1
      simp [ext_tvar]
    simp [PType.tsubst_weaken_tvar_comm]

lemma PType.tsubst_comp (T : PType n m1) (g1 : TypeMap n m1 m2) (g2 : TypeMap n m2 m3) :
  (T.tsubst g1).tsubst g2 = T.tsubst (g1.map (fun P => P.tsubst g2)) :=
  match T with
  | PType.tvar X => by simp [tsubst, TypeMap.map]
  | PType.arr (CType.capt C1 S1) (CType.capt C2 S2) => by
    have ih1 := PType.tsubst_comp S1 g1 g2
    have ih2 := PType.tsubst_comp S2 g1.ext_var g2.ext_var
    simp [tsubst, ih1]
    simp [TypeMap.ext_var_comp]
    simp [ih2]
  | PType.arr CType.cap (CType.capt C2 S2) => by
    have ih2 := PType.tsubst_comp S2 g1.ext_var g2.ext_var
    simp [tsubst, CType.tsubst]
    simp [TypeMap.ext_var_comp]
    simp [ih2]
  | PType.arr (CType.capt C1 S1) CType.cap => by
    have ih1 := PType.tsubst_comp S1 g1 g2
    simp [tsubst, ih1]
    simp [TypeMap.ext_var_comp]
    simp [CType.tsubst]
  | PType.arr CType.cap CType.cap => by
    simp [tsubst]
    simp [TypeMap.ext_var_comp]
    simp [CType.tsubst]
  | PType.tarr S1 (CType.capt C2 S2) => by
    have ih1 := PType.tsubst_comp S1 g1 g2
    have ih2 := PType.tsubst_comp S2 g1.ext_tvar g2.ext_tvar
    simp [tsubst, ih1]
    simp [TypeMap.ext_tvar_comp]
    simp [ih2]
  | PType.tarr S1 CType.cap => by
    have ih1 := PType.tsubst_comp S1 g1 g2
    simp [tsubst, ih1]
    simp [TypeMap.ext_tvar_comp]
    simp [CType.tsubst]
  | PType.top => by
    simp [tsubst, TypeMap.map]
  | PType.boxed (CType.capt C1 S1) => by
    have ih := PType.tsubst_comp S1 g1 g2
    simp [tsubst, ih]
  | PType.boxed CType.cap => by
    simp [tsubst, CType.tsubst]

lemma CType.tsubst_comp (T : CType n m1) (g1 : TypeMap n m1 m2) (g2 : TypeMap n m2 m3) :
  (T.tsubst g1).tsubst g2 = T.tsubst (g1.map (fun P => P.tsubst g2)) := by
  cases T <;> simp [tsubst]
  simp [PType.tsubst_comp]

lemma PType.open_tvar_def {n m : Nat} (S : PType n m.succ) {R} :
  S.open_tvar R = S.tsubst (tvar_open_map R) := rfl

lemma CType.open_tvar_def {n m : Nat} (T : CType n m.succ) {R} :
  T.open_tvar R = T.tsubst (tvar_open_map R) := rfl

lemma TypeMap.tsubst_open_tvar_map_comm (S : PType n m1) (g : TypeMap n m1 m2) :
  (tvar_open_map S).map (fun P => P.tsubst g) = g.ext_tvar.map (fun P => P.tsubst (tvar_open_map (S.tsubst g))) := by
  funext X
  simp [map]
  cases X using Fin.cases with
  | H0 =>
    simp [ext_tvar]
    conv =>
      lhs
      simp [tvar_open_map]
  | Hs X0 =>
    simp [ext_tvar]
    conv =>
      lhs
      simp [tvar_open_map]
      simp [PType.tsubst]
    rw [<- PType.open_tvar_def]
    simp [PType.open_tvar_weaken_tvar_id]

lemma CType.tsubst_open_tvar_comm (T : CType n m1.succ) (S : PType n m1) (g : TypeMap n m1 m2) :
  (T.open_tvar S).tsubst g = (T.tsubst g.ext_tvar).open_tvar (S.tsubst g) := by
  unfold open_tvar
  simp [CType.tsubst_comp]
  simp [TypeMap.tsubst_open_tvar_map_comm]
