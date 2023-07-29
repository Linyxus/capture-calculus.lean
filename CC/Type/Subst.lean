import CC.Basic
import CC.Type
import CC.Context
import CC.Subst

namespace CC

def PType.tsubst (S : PType n m.succ) (σ : OpenMap n m) : PType n m :=
  match S with
  | PType.tvar X => σ X
  | PType.top => PType.top
  | PType.arr (CType.capt C1 S1) (CType.capt C2 S2) =>
    PType.arr (CType.capt C1 (S1.tsubst σ)) (CType.capt C2 (S2.tsubst σ.ext_var))
  | PType.tarr S1 (CType.capt C2 S2) =>
    PType.tarr (S1.tsubst σ) (CType.capt C2 (S2.tsubst σ.ext_tvar))
  | PType.boxed (CType.capt C1 S1) =>
    PType.boxed (CType.capt C1 (S1.tsubst σ))

def CType.tsubst (T : CType n m.succ) (σ : OpenMap n m) : CType n m :=
  match T with
  | CType.capt C S => CType.capt C (S.tsubst σ)

def CType.open_tvar (T : CType n m.succ) (R : PType n m) : CType n m :=
  T.tsubst (tvar_open_map R)
