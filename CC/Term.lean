import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import CC.CaptureSet
import CC.Basic
import CC.CaptureSet
import CC.Type

namespace CC

inductive LetMode : Type where
| par : LetMode
| seq : LetMode

inductive Term : Nat -> Nat -> Type where
| var : Fin n -> Term n m
| abs : Finset (Fin n) -> CType n m -> Term n.succ m -> Term n m
| app : Fin n -> Fin n -> Term n m
| tabs : PType n m -> Term n m.succ -> Term n m
| tapp : Fin n -> PType n m -> Term n m
| box : Fin n -> Term n m
| unbox : CaptureSet n -> Fin n -> Term n m
| letval : LetMode -> Term n m -> Term n.succ m -> Term n m
| letvar : SepDegree n -> Fin n -> Term n.succ m -> Term n m
| reader : Fin n -> Term n m
| read : Fin n -> Term n m
| write : Fin n -> Fin n -> Term n m

def Term.rename (t : Term n1 m1) (f : VarMap n1 n2) (g : VarMap m1 m2) : Term n2 m2 :=
  match t with
  | Term.var x => Term.var (f x)
  | Term.abs D T t => Term.abs (D.image f) (T.rename f g) (t.rename f.ext g)
  | Term.app x y => Term.app (f x) (f y)
  | Term.tabs S t => Term.tabs (S.rename f g) (t.rename f g.ext)
  | Term.tapp x S => Term.tapp (f x) (S.rename f g)
  | Term.box x => Term.box (f x)
  | Term.unbox C x => Term.unbox (C.rename f) (f x)
  | Term.letval m t u => Term.letval m (t.rename f g) (u.rename f.ext g)
  | Term.letvar D x t => Term.letvar (D.rename f) (f x) (t.rename f.ext g)
  | Term.reader x => Term.reader (f x)
  | Term.read x => Term.read (f x)
  | Term.write x y => Term.write (f x) (f y)

inductive Value : Term n m -> Prop where
| abs : Value (Term.abs D T t)
| tabs : Value (Term.tabs S t)
| box : Value (Term.box x)
| reader : Value (Term.reader x)

structure Val (n m : Nat) where
  t : Term n m
  isVal : Value t

def Value.rename {t : Term n1 m1} (v : Value t) 
  (f : VarMap n1 n2) (g : VarMap m1 m2) :
  Value (t.rename f g) := by
  cases v <;> (simp [Term.rename]; constructor)

def Term.weaken_var (t : Term n m) : Term n.succ m :=
  t.rename weaken_map id

def Term.weaken_var1 (t : Term (Nat.succ n) m) : Term n.succ.succ m :=
  t.rename weaken_map.ext id

def Term.weaken_tvar (t : Term n m) : Term n m.succ :=
  t.rename id weaken_map

def Term.open_var (t : Term n.succ m) (x : Fin n) : Term n m :=
  t.rename (open_map x) id

def Value.weaken_var {t : Term n m} (v : Value t) : Value (Term.weaken_var t) :=
  v.rename weaken_map id

def Val.weaken_var (v : Val n m) : Val n.succ m :=
  { t := v.t.weaken_var, isVal := v.isVal.weaken_var }

def Term.rename_id (t : Term n m) : t.rename id id = t := by
  induction t <;> try (solve | simp [rename] | simp [rename]; aesop)
