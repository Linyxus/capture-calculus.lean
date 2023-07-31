import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import CC.CaptureSet
import CC.Basic
import CC.CaptureSet
import CC.Type

namespace CC

inductive Term : Nat -> Nat -> Type where
| var : Fin n -> Term n m
| abs : CType n m -> Term n.succ m -> Term n m
| app : Fin n -> Fin n -> Term n m
| tabs : PType n m -> Term n m.succ -> Term n m
| tapp : Fin n -> PType n m -> Term n m
| box : Fin n -> Term n m
| unbox : CaptureSet n -> Fin n -> Term n m
| letval : Term n m -> Term n.succ m -> Term n m

def Term.rename (t : Term n1 m1) (f : VarMap n1 n2) (g : VarMap m1 m2) : Term n2 m2 :=
  match t with
  | Term.var x => Term.var (f x)
  | Term.abs T t => Term.abs (T.rename f g) (t.rename f.ext g)
  | Term.app x y => Term.app (f x) (f y)
  | Term.tabs S t => Term.tabs (S.rename f g) (t.rename f g.ext)
  | Term.tapp x S => Term.tapp (f x) (S.rename f g)
  | Term.box x => Term.box (f x)
  | Term.unbox C x => Term.unbox (C.rename f) (f x)
  | Term.letval t u => Term.letval (t.rename f g) (u.rename f.ext g)

inductive Value : Term n m -> Prop where
| abs : Value (Term.abs T t)
| tabs : Value (Term.tabs S t)
| box : Value (Term.box x)

def Value.rename {t : Term n1 m1} (v : Value t) 
  (f : VarMap n1 n2) (g : VarMap m1 m2) :
  Value (t.rename f g) := by
  cases v <;> (simp [Term.rename]; constructor)

def Term.weaken_var (t : Term n m) : Term n.succ m :=
  t.rename weaken_map id

def Term.weaken_tvar (t : Term n m) : Term n m.succ :=
  t.rename id weaken_map

def Term.open_var (t : Term n.succ m) (x : Fin n) : Term n m :=
  t.rename (open_map x) id

def Term.open_tvar (t : Term n m.succ) (X : Fin m) : Term n m :=
  t.rename id (open_map X)

-- def Term.cv' (k : Nat) (t : Term (n + k) m) : Finset (Fin n) :=
--   match t with
--   | Term.var x => if k <= x then {sorry} else {}
--   | Term.abs T t => t.cv' k.succ
--   | Term.app x y => sorry
--   | Term.tabs S t => sorry
--   | Term.tapp x S => sorry
--   | Term.box x => sorry
--   | Term.unbox C x => sorry
--   | Term.letval t u => sorry
