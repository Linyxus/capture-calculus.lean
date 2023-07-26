import CC.CaptureSet
import CC.Basic

namespace CC

mutual

inductive PType : Nat -> Nat -> Type where
| tvar  : Fin m -> PType n m
| top   : PType n m
| arr   : CType n m -> CType n.succ m -> PType n m
| tarr  : PType n m -> CType n m.succ -> PType n m
| boxed : CType n m -> PType n m

inductive CType : Nat -> Nat -> Type where
| capt :
  CaptureSet n ->
  PType n m ->
  CType n m

end

def PType.rename (S : PType n1 m1) (f : VarMap n1 n2) (g : VarMap m1 m2) : PType n2 m2 :=
  match S with
  | PType.tvar x => PType.tvar (g x)
  | PType.top => PType.top
  | PType.arr (CType.capt C1 S1) (CType.capt C2 S2) => 
    PType.arr (CType.capt (C1.rename f) (S1.rename f g)) (CType.capt (C2.rename f.ext) (S2.rename f.ext g))
  | PType.tarr S (CType.capt C R) => 
    PType.tarr (S.rename f g) (CType.capt (C.rename f) (R.rename f g.ext))
  | PType.boxed (CType.capt C R) => PType.boxed (CType.capt (C.rename f) (R.rename f g))

def CType.rename (T : CType n1 m1) (f : VarMap n1 n2) (g : VarMap m1 m2) : CType n2 m2 :=
  match T with
  | CType.capt C S => CType.capt (C.rename f) (S.rename f g)

def PType.weaken_var (S : PType n m) : PType n.succ m :=
  S.rename weaken_map id

def PType.weaken_tvar (S : PType n m) : PType n m.succ :=
  S.rename id weaken_map

def CType.weaken_var (T : CType n m) : CType n.succ m :=
  T.rename weaken_map id

def CType.weaken_tvar (T : CType n m) : CType n m.succ :=
  T.rename id weaken_map

@[simp]
theorem rename_capt :
  (CType.capt C S).rename f g = CType.capt (C.rename f) (S.rename f g) :=
  rfl

@[simp]
theorem rename_arr :
  (PType.arr T1 T2).rename f g = PType.arr (T1.rename f g) (T2.rename f.ext g) := by
  cases T1
  cases T2
  simp [PType.rename]

@[simp]
theorem rename_tarr :
  (PType.tarr T1 T2).rename f g = PType.tarr (T1.rename f g) (T2.rename f g.ext) := by
  cases T2
  simp [PType.rename]

@[simp]
theorem rename_boxed :
  (PType.boxed T).rename f g = PType.boxed (T.rename f g) := by
  cases T
  simp [PType.rename]

@[simp]
theorem PType.rename_id : (S : PType n m) -> S.rename id id = S
| PType.tvar x => by simp [PType.rename]
| PType.top => by simp [PType.rename]
| PType.arr (CType.capt C1 S1) (CType.capt C2 S2) => by
  simp [PType.rename]
  have ih1 := PType.rename_id S1
  have ih2 := PType.rename_id S2
  aesop
| PType.tarr S (CType.capt C R) => by
  simp [PType.rename]
  have ih1 := PType.rename_id S
  have ih2 := PType.rename_id R
  aesop
| PType.boxed (CType.capt C R) => by
  simp [PType.rename]
  have ih := PType.rename_id R; aesop

@[simp]
theorem CType.rename_id : (T : CType n m) -> T.rename id id = T
| CType.capt C S => by
  simp [CType.rename]

theorem PType.rename_comp
  {f1 : VarMap n1 n2} {f2 : VarMap n2 n3}
  {g1 : VarMap m1 m2} {g2 : VarMap m2 m3} :
  (S : PType n1 m1) ->
  (S.rename f1 g1).rename f2 g2 = S.rename (f2.comp f1) (g2.comp g1)
| PType.tvar X => by
  unfold VarMap.comp
  simp [PType.rename]
| PType.top => by simp [PType.rename]
| PType.arr (CType.capt C1 S1) (CType.capt C2 S2) => by
  simp [PType.rename]
  simp [CaptureSet.rename_comp]
  simp [ext_comp]
  apply And.intro <;> apply PType.rename_comp
| PType.tarr S (CType.capt C R) => by
  simp [PType.rename]
  simp [CaptureSet.rename_comp]
  simp [ext_comp]
  apply And.intro <;> apply PType.rename_comp
| PType.boxed (CType.capt C R) => by
  simp [PType.rename]
  simp [CaptureSet.rename_comp]
  apply PType.rename_comp

theorem CType.rename_comp
  {f1 : VarMap n1 n2} {f2 : VarMap n2 n3}
  {g1 : VarMap m1 m2} {g2 : VarMap m2 m3} :
  (T : CType n1 m1) ->
  (T.rename f1 g1).rename f2 g2 = T.rename (f2.comp f1) (g2.comp g1)
| CType.capt C R => by
  simp [CaptureSet.rename_comp, PType.rename_comp]
