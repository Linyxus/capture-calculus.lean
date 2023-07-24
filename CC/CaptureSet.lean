import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import CC.Basic

namespace CC

structure CaptureSet (n : Nat) where
  elems : Finset (Fin n)

instance : Membership (Fin n) (CaptureSet n) :=
  ⟨fun a s => a ∈ s.1⟩

instance : Singleton (Fin n) (CaptureSet n) :=
  ⟨fun x => ⟨{x}⟩⟩ 

def CaptureSet.rename (C : CaptureSet n1) (f : VarMap n1 n2) : CaptureSet n2 :=
  ⟨C.elems.image f⟩  
  
def CaptureSet.weaken_var (C : CaptureSet n) : CaptureSet n.succ :=
  C.rename weaken_map
