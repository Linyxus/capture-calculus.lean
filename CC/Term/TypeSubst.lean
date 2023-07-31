import CC.Basic
import CC.Term
import CC.Context
import CC.TypeMap
import CC.Type.TypeSubst

namespace CC

def Term.tsubst (t : Term n m1) (σ : TypeMap n m1 m2) : Term n m2 :=
  match t with
  | Term.var x => Term.var x
  | Term.abs T t => Term.abs (T.tsubst σ) (t.tsubst σ.ext_var)
  | Term.tabs S t => Term.tabs (S.tsubst σ) (t.tsubst σ.ext_tvar)
  | Term.app x y => Term.app x y
  | Term.tapp x S => Term.tapp x (S.tsubst σ)
  | Term.box x => Term.box x
  | Term.unbox C x => Term.unbox C x
  | Term.letval t u => Term.letval (t.tsubst σ) (u.tsubst σ.ext_var)

def Term.open_tvar (t : Term n m.succ) (R : PType n m) : Term n m :=
  t.tsubst (tvar_open_map R)
