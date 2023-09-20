
inductive BiFin : Nat -> Nat -> Type where
| injn : Fin n -> BiFin n k
| injk : Fin k -> BiFin n k
