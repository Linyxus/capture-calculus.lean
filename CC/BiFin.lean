
inductive BiFin : Nat -> Nat -> Type where
| injn : Fin n -> BiFin n k
| injk : Fin k -> BiFin n k

def BiFin.instDecEq (n k : Nat) : DecidableEq (BiFin n k)
| injn i, injn j =>
  match (decEq i j) with
  | isTrue p => isTrue (congrArg injn p)
  | isFalse p => isFalse (fun h => by cases h; apply p; rfl)
| injk i, injk j =>
  match (decEq i j) with
  | isTrue p => isTrue (congrArg injk p)
  | isFalse p => isFalse (fun h => by cases h; apply p; rfl)
| injn i, injk j => isFalse (fun h => by cases h)
| injk i, injn j => isFalse (fun h => by cases h)

instance (n k : Nat) : DecidableEq (BiFin n k) := BiFin.instDecEq n k
