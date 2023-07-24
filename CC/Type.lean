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
    PType.arr (CType.capt (C1.rename f) (S1.rename f g)) (CType.capt (C2.rename (extv f)) (S2.rename (extv f) g))
  | PType.tarr S (CType.capt C R) => 
    PType.tarr (S.rename f g) (CType.capt (C.rename f) (R.rename f (extv g)))
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
