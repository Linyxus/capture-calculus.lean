import CC.Basic
import CC.Term
import CC.Context
import CC.TypeMap
import CC.Type.TypeSubst

namespace CC

def Term.tsubst (t : Term n m1) (σ : TypeMap n m1 m2) : Term n m2 :=
  match t with
  | Term.var x => Term.var x
  | Term.abs D T t => Term.abs D (T.tsubst σ) (t.tsubst σ.ext_var)
  | Term.tabs S t => Term.tabs (S.tsubst σ) (t.tsubst σ.ext_tvar)
  | Term.app x y => Term.app x y
  | Term.tapp x S => Term.tapp x (S.tsubst σ)
  | Term.box x => Term.box x
  | Term.unbox C x => Term.unbox C x
  | Term.letval m t u => Term.letval m (t.tsubst σ) (u.tsubst σ.ext_var)
  | Term.letvar D x t => Term.letvar D x (t.tsubst σ.ext_var)
  | Term.reader x => Term.reader x
  | Term.read x => Term.read x
  | Term.write x y => Term.write x y

def Term.open_tvar (t : Term n m.succ) (R : PType n m) : Term n m :=
  t.tsubst (tvar_open_map R)

@[simp]
lemma Term.tsubst_id (t : Term n m) :
  t.tsubst TypeMap.id = t := by
  induction t <;> try (solve | simp [Term.tsubst, *, CType.tsubst_id, PType.tsubst_id])

lemma Value.tsubst (v : Value t) :
  Value (t.tsubst g) := by
  cases v <;> constructor
