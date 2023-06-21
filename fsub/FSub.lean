-- System FSub in MNF
import Mathlib.Data.Fin.Basic

namespace FSub

open Nat

inductive Typ : Nat -> Type where
| top : Typ n
| tvar : Fin n -> Typ n
| func : Typ n -> Typ n -> Typ n
| poly : Typ n -> Typ n.succ -> Typ n

open Typ

inductive Ctx : Nat -> Nat -> Type where
| empty : Ctx 0 0
| extend_var : Ctx m n -> Typ n -> Ctx m.succ n
| extend_tvar : Ctx m n -> Typ n -> Ctx m n.succ

open Ctx

def shift_tvar : ∀ {n}, Fin n -> Nat -> Fin n.succ
| n+1 , x , 0 => x.succ
| n+1 , x , Nat.succ k =>
  by 
    cases x using Fin.cases with
    | H0 => exact 0
    | Hs i => exact (shift_tvar i k).succ

def shift_typ : Typ n -> Nat -> Typ n.succ
| top , _ => top
| tvar x , k => tvar (shift_tvar x k)
| func S T , k => func (shift_typ S k) (shift_typ T k)
| poly S T , k => poly (shift_typ S k) (shift_typ T k.succ)

inductive LookupTVar : Ctx m n -> Fin n -> Typ n -> Type where
| lt_here :
  LookupTVar (extend_tvar Γ T) 0 (shift_typ T 0)
| lt_there_tvar :
  LookupTVar Γ x T ->
  LookupTVar (extend_tvar Γ S) x.succ (shift_typ T 0)
| lt_there_var :
  LookupTVar Γ x T ->
  LookupTVar (extend_var Γ S) x T

inductive LookupVar : Ctx m n -> Fin m -> Typ n -> Type where
| lv_here :
  LookupVar (extend_var Γ T) 0 T
| lv_there_tvar :
  LookupVar Γ x T ->
  LookupVar (extend_tvar Γ S) x (shift_typ T 0)
| lv_there_var :
  LookupVar Γ x T ->
  LookupVar (extend_var Γ S) (Fin.succ x) T

inductive subtype : Ctx m n -> Typ n -> Typ n -> Type where
| sub_refl :
  --------------
  subtype Γ T T
| sub_trans :
  subtype Γ S T ->
  subtype Γ T U ->
  ------------------
  subtype Γ S U
| sub_top :
  -----------------
  subtype Γ T top
| sub_tvar : ∀ {Γ : Ctx m n} {X : Fin n} {T : Typ n},
  LookupTVar Γ X T ->
  -----------------
  subtype Γ (tvar X) T
| sub_func :
  subtype Γ S2 S1 ->
  subtype Γ T1 T2 ->
  --------------------
  subtype Γ (func S1 T1) (func S2 T2)
| sub_poly :
  subtype Γ S2 S1 ->
  subtype (extend_tvar Γ S2) T1 T2 ->
  -------------------------------
  subtype Γ (poly S1 T1) (poly S2 T2)

def rmap (n1 n2 : Nat) : Type := Fin n1 -> Fin n2

def rmap_ext (f : rmap n1 n2) : rmap n1.succ n2.succ := 
  fun x =>
    by 
      cases x using Fin.cases with
      | H0 => exact 0
      | Hs i => exact (f i).succ

def rmap_ext_n (f : rmap n1 n2) : (n : Nat) -> rmap (n1 + n) (n2 + n)
| 0 => f
| Nat.succ n => rmap_ext (rmap_ext_n f n)

def succ_rmap_ext_n {n} : (m : Nat) -> rmap (n + m) (n + m).succ
| 0 => Fin.succ
| Nat.succ m => rmap_ext (succ_rmap_ext_n m)

def rmap_ext_succ_n (f : rmap n1 n2) : (n : Nat) -> rmap (n1 + n).succ (n2 + n).succ
| 0 => rmap_ext f
| Nat.succ n => rmap_ext (rmap_ext_succ_n f n)

def ren_typ (f : rmap n1 n2) : Typ n1 -> Typ n2
| top => top
| tvar x => tvar (f x)
| func S T => func (ren_typ f S) (ren_typ f T)
| poly S T => poly (ren_typ f S) (ren_typ (rmap_ext f) T)

def lift_typ : Typ n -> Typ n.succ := ren_typ Fin.succ

def tsmap (n1 n2 : Nat) : Type := Fin n1 -> Typ n2

def tsmap_ext (f : tsmap n1 n2) : tsmap n1.succ n2.succ :=
  fun x =>
    by
      cases x using Fin.cases with
      | H0 => exact (tvar 0)
      | Hs n1 => exact (lift_typ (f n1))

def tsmap_ext_n (f : tsmap n.succ n) : (m : Nat) -> tsmap (succ (n + m)) (n + m)
| 0 => f
| Nat.succ n => tsmap_ext (tsmap_ext_n f n)

def tsmap_ext_n' (f : tsmap n1 n2) : (n : Nat) -> tsmap (n1 + n) (n2 + n)
| 0 => f
| Nat.succ n => tsmap_ext (tsmap_ext_n' f n)

def tsmap_ext_succ_n (f : tsmap n1 n2) : (n : Nat) -> tsmap (n1 + n).succ (n2 + n).succ
| 0 => tsmap_ext f
| Nat.succ n => tsmap_ext (tsmap_ext_succ_n f n)

def tsub_typ (g : tsmap n1 n2) : Typ n1 -> Typ n2
| top => top
| tvar x => g x
| func S T => func (tsub_typ g S) (tsub_typ g T)
| poly S T => poly (tsub_typ g S) (tsub_typ (tsmap_ext g) T)

def open_typ_tsmap (S : Typ n) : tsmap n.succ n :=
  fun x =>
    by 
      cases x using Fin.cases with
      | H0 => exact S
      | Hs n => exact tvar n

def open_typ (S : Typ n) : Typ n.succ -> Typ n :=
  tsub_typ (open_typ_tsmap S)

theorem ren_lift_comm_var (f : rmap n1 n2) :
  ∀ n X,
    (rmap_ext_succ_n f n) (succ_rmap_ext_n n X) = succ_rmap_ext_n n (rmap_ext_n f n X)
| zero , X =>
  by
    simp [succ_rmap_ext_n, rmap_ext_succ_n, rmap_ext, rmap_ext_n]
| Nat.succ n , X =>
  by
    simp [succ_rmap_ext_n, rmap_ext_succ_n, rmap_ext_n]
    cases X using Fin.cases with
    | H0 => rfl
    | Hs i =>
      conv =>
        pattern (rmap_ext _ (Fin.succ i))
        simp [rmap_ext]
      conv =>
        pattern (rmap_ext _ (Fin.succ i))
        simp [rmap_ext]
      conv =>
        lhs
        apply congrFun
        apply congrFun
        simp [rmap_ext]
      simp
      conv =>
        rhs
        apply congrFun; apply congrFun
        simp [rmap_ext]
      simp
      apply ren_lift_comm_var


theorem ren_lift_comm_typ (f : rmap n1 n2) :
  ∀ n S,
    ren_typ (rmap_ext_succ_n f n) (ren_typ (succ_rmap_ext_n n) S) =
      ren_typ (succ_rmap_ext_n n) (ren_typ (rmap_ext_n f n) S)
| n , top => rfl
| n , tvar X =>
  by
    simp [ren_typ]
    apply ren_lift_comm_var
| n , func S T =>
  by
    simp [ren_typ]
    apply And.intro
    {
      apply (ren_lift_comm_typ (S := S))
    }
    {
      apply (ren_lift_comm_typ (S := T))
    }
| n , poly S T =>
  by
    simp [ren_typ]
    apply And.intro
    {
      apply (ren_lift_comm_typ (S := S))
    }
    {
      apply (ren_lift_comm_typ (n := n.succ) (S := T))
    }

theorem ren_lift_comm_typ' :
  ∀ (f : rmap n1 n2) S,
    ren_typ (rmap_ext f) (lift_typ S) = lift_typ (ren_typ f S) :=
  by
    intro f S
    apply (ren_lift_comm_typ (n := 0))

theorem tsub_lift_comm_tvar (g : tsmap n1 n2) :
  ∀ n (X : Fin (n1 + n)),
    (tsmap_ext_succ_n g n) (succ_rmap_ext_n n X) = ren_typ (succ_rmap_ext_n n) (tsmap_ext_n' g n X)
| 0   , X =>
  by
    simp [tsmap_ext_succ_n, succ_rmap_ext_n, tsmap_ext_n', tsmap_ext, lift_typ]
| Nat.succ n , X =>
  by
    simp [tsmap_ext_succ_n, succ_rmap_ext_n, tsmap_ext_n']
    cases X using Fin.cases with
    | H0 =>
      conv =>
        pattern (rmap_ext _ 0)
        simp [rmap_ext]
    | Hs X0 =>
      conv =>
        pattern (rmap_ext _ (Fin.succ _))
        simp [rmap_ext]
      conv =>
        pattern (tsmap_ext _ (Fin.succ X0))
        simp [tsmap_ext]
      simp [tsmap_ext]
      rw [ren_lift_comm_typ']
      simp [tsub_lift_comm_tvar]

theorem tsub_lift_comm_typ (g : tsmap n1 n2) :
  ∀ n S,
    tsub_typ (tsmap_ext_succ_n g n) (ren_typ (succ_rmap_ext_n n) S) = ren_typ (succ_rmap_ext_n n) (tsub_typ (tsmap_ext_n' g n) S)
| n , top => rfl
| n , tvar X =>
  by 
    simp [ren_typ, tsub_typ]
    apply tsub_lift_comm_tvar
| n , func P Q =>
  by
    simp [ren_typ, tsub_typ]
    apply And.intro
    {
      apply (tsub_lift_comm_typ (S := P))
    }
    {
      apply (tsub_lift_comm_typ (S := Q))
    }
| n , poly S T =>
  by
    simp [ren_typ, tsub_typ]
    apply And.intro; apply (tsub_lift_comm_typ (S := S)); apply (tsub_lift_comm_typ (n := n.succ) (S := T))

theorem tsub_lift_comm_typ' :
  ∀ (g : tsmap n1 n2) S,
    tsub_typ (tsmap_ext g) (lift_typ S) = lift_typ (tsub_typ g S) :=
  by
    intro g S
    apply (tsub_lift_comm_typ (n := 0))

theorem ren_tsub_comm_var (f : rmap n1 n2) (S : Typ n1) :
  ∀ n (X : Fin (n1 + n).succ),
    ren_typ (rmap_ext_n f n) (tsmap_ext_n (open_typ_tsmap S) n X) =
      tsmap_ext_n (open_typ_tsmap (ren_typ f S)) n (rmap_ext_n f n.succ X)
| 0 , X =>
  by simp [rmap_ext_n, tsmap_ext_n, ren_typ]
     cases X using Fin.cases with
      | H0 => rfl
      | Hs i => rfl
| Nat.succ n , X =>
  by simp [rmap_ext_n, tsmap_ext_n]
     cases X using Fin.cases with
      | H0 => rfl
      | Hs i =>
        conv =>
          pattern (tsmap_ext _ (Fin.succ n))
          simp [tsmap_ext]
        conv =>
          pattern (rmap_ext _ (Fin.succ _))
          apply congrFun; apply congrFun
          simp [rmap_ext] 
        simp
        conv =>
          rhs
          simp [tsmap_ext]
        simp [ren_lift_comm_typ']
        rw [ren_tsub_comm_var (n := n)]
        simp [rmap_ext_n]

theorem ren_tsub_comm (f : rmap n1 n2) (S : Typ n1) :
  ∀ n (T : Typ (n1 + n).succ), 
    ren_typ (rmap_ext_n f n) (tsub_typ (tsmap_ext_n (open_typ_tsmap S) n) T) =
      tsub_typ (tsmap_ext_n (open_typ_tsmap (ren_typ f S)) n) (ren_typ (rmap_ext_n f n.succ) T)
| n , top => rfl
| n , tvar X =>
  by
    simp [ren_typ, tsub_typ]
    apply ren_tsub_comm_var
| n , func T U =>
  by
    simp [ren_typ, tsub_typ]
    apply And.intro
    {
      apply (ren_tsub_comm (T := T))
    }
    {
      apply (ren_tsub_comm (T := U))
    }
| n , poly T U =>
  by
    simp [ren_typ, tsub_typ]
    apply And.intro
    {
      apply (ren_tsub_comm (T := T))
    }
    {
      apply (ren_tsub_comm (n := n.succ) (T := U))
    }

theorem ren_tsub_comm' (f : rmap n1 n2) (S : Typ n1) :
  ∀ (T : Typ n1.succ), 
    ren_typ f (open_typ S T) =
      open_typ (ren_typ f S) (ren_typ (rmap_ext f) T) :=
  by
    intro T
    apply (ren_tsub_comm (n := 0))

inductive var : Ctx m n -> Fin m -> Typ n -> Type where
| var :
  LookupVar Γ x T ->
  subtype Γ T U ->
  ----------------
  var Γ x U

inductive term : Ctx m n -> Typ n -> Type where
| var :
  var Γ x T ->
  --------------------
  term Γ T
| app :
  var Γ x (func S T) ->
  var Γ y S ->
  --------------------
  term Γ T
| tapp :
  var Γ x (poly S T) ->
  ----------------------
  term Γ (open_typ S T)
| abs :
  term (extend_var Γ S) T ->
  ------------------------
  term Γ (func S T)
| tabs :
  term (extend_tvar Γ S) T ->
  --------------------------
  term Γ (poly S T)
| sub :
  term Γ S ->
  subtype Γ S T ->
  ---------------
  term Γ T
| letb :
  term Γ S ->
  term (extend_var Γ S) T ->
  ---------------------------
  term Γ T

def ptmap (Γ : Ctx m1 n1) (f : rmap n1 n2) (Δ : Ctx m2 n2) :=
  ∀ {X S}, LookupTVar Γ X S -> LookupTVar Δ (f X) (ren_typ f S)

def pemap (Γ : Ctx m1 n1) (f : rmap m1 m2) (g : rmap n1 n2) (Δ : Ctx m2 n2) :=
  ∀ {x T}, LookupVar Γ x T -> LookupVar Δ (f x) (ren_typ g T)

def pemap_ext_var (f : rmap m1 m2) (g : rmap n1 n2) (ρ : pemap Γ f g Δ) S :
  pemap (extend_var Γ S) (rmap_ext f) g (extend_var Δ (ren_typ g S))
| _ , _ , LookupVar.lv_here => LookupVar.lv_here
| _ , _ , LookupVar.lv_there_var L' =>
  by
    simp [rmap_ext]
    apply LookupVar.lv_there_var
    aesop

def ptmap_ext_var (f : rmap n1 n2) (ρ : ptmap Γ f Δ) S :
  ptmap (extend_var Γ S) f (extend_var Δ (ren_typ f S)) :=
  by
    intro X S' L
    cases L with
    | lt_there_var L' =>
      apply LookupTVar.lt_there_var
      aesop

theorem shift_lift_eq_tvar :
  ∀ k (X : Fin (n + k)),
    shift_tvar X k = succ_rmap_ext_n k X
| 0 , X => 
  by
    cases n
    { apply Fin.elim0; assumption }
    {
      simp [shift_tvar, succ_rmap_ext_n]
    }
| k+1, X =>
  by 
    simp [shift_tvar, succ_rmap_ext_n, shift_lift_eq_tvar]
    cases X using Fin.cases with
    | H0 =>
      simp [Fin.cases, rmap_ext]
    | Hs X0 =>
      simp [Fin.cases, rmap_ext]
      apply (shift_lift_eq_tvar (k:=k))

theorem shift_lift_eq_typ :
  ∀ k (T : Typ (n + k)),
    shift_typ T k = ren_typ (succ_rmap_ext_n k) T
| k , top => rfl
| k , tvar X => by simp [shift_typ, ren_typ, shift_lift_eq_tvar]
| k , func P Q =>
  by 
    simp [shift_typ, ren_typ]
    apply And.intro <;> apply shift_lift_eq_typ
| k , poly P Q =>
  by
    simp [shift_typ, ren_typ]
    apply And.intro
    {
      apply (shift_lift_eq_typ (T := P))
    }
    {
      apply (shift_lift_eq_typ (k := k.succ) (T := Q))
    }

theorem shift_lift_eq_typ' :
  ∀ (T : Typ n),
    shift_typ T 0 = ren_typ Fin.succ T :=
  by
    intro T
    have H :
      ∀ {n} (T : Typ n), 
        ren_typ (succ_rmap_ext_n 0) T = ren_typ Fin.succ T :=
        by
          intro n T
          simp [succ_rmap_ext_n]
    rw [<- H]
    apply shift_lift_eq_typ (k := 0)

theorem ren_shift_comm_typ (f : rmap n1 n2) :
  ∀ T, ren_typ (rmap_ext f) (shift_typ T 0) = shift_typ (ren_typ f T) 0 :=
  by
    intro T
    rw [shift_lift_eq_typ (k := 0)]
    rw [shift_lift_eq_typ (k := 0)]
    have H : ∀ (f : rmap n1 n2), rmap_ext f = rmap_ext_succ_n f 0 := 
      by
        intro f
        simp [rmap_ext_succ_n]
    rw [H]
    rw [ren_lift_comm_typ]
    simp [rmap_ext_succ_n]
    rfl

theorem tsub_shift_comm_typ (g : tsmap n1 n2) :
  ∀ T, tsub_typ (tsmap_ext g) (shift_typ T 0) = shift_typ (tsub_typ g T) 0 :=
  by
    intro T
    rw [shift_lift_eq_typ (k := 0)]
    rw [shift_lift_eq_typ (k := 0)]
    have H : ∀ (g : tsmap n1 n2), tsmap_ext g = tsmap_ext_succ_n g 0 := 
      by
        intro g
        simp [tsmap_ext_succ_n]
    rw [H]
    rw [tsub_lift_comm_typ]
    simp [rmap_ext_succ_n]
    rfl

def pemap_ext_tvar (f : rmap m1 m2) (g : rmap n1 n2) (ρ : pemap Γ f g Δ) S :
  pemap (extend_tvar Γ S) f (rmap_ext g) (extend_tvar Δ (ren_typ g S)) :=
  by
    intro x T L
    cases L with
    | lv_there_tvar L' =>
      rw [ren_shift_comm_typ]
      apply LookupVar.lv_there_tvar
      apply ρ
      assumption

def ptmap_ext_tvar (f : rmap n1 n2) (ρ : ptmap Γ f Δ) S :
  ptmap (extend_tvar Γ S) (rmap_ext f) (extend_tvar Δ (ren_typ f S)) :=
  by
    intro X P L
    cases L with
    | lt_here =>
      rw [ren_shift_comm_typ]
      apply LookupTVar.lt_here
    | lt_there_tvar L' =>
      rw [ren_shift_comm_typ]
      apply LookupTVar.lt_there_tvar
      apply ρ
      assumption

def tsub_sub (g : rmap n1 n2) (ρ1 : pemap Γ f g Δ) (ρ2 : ptmap Γ g Δ) : subtype Γ T U -> subtype Δ (ren_typ g T) (ren_typ g U)
| subtype.sub_refl => subtype.sub_refl
| subtype.sub_top => subtype.sub_top
| subtype.sub_func P Q =>
  subtype.sub_func (tsub_sub g ρ1 ρ2 P) (tsub_sub g ρ1 ρ2 Q)
| subtype.sub_poly P Q =>
  subtype.sub_poly (tsub_sub g ρ1 ρ2 P) (tsub_sub (rmap_ext g) (pemap_ext_tvar f g ρ1 _) (ptmap_ext_tvar g ρ2 _) Q)
| subtype.sub_tvar L =>
  subtype.sub_tvar (ρ2 L)
| subtype.sub_trans P Q =>
  by
    apply subtype.sub_trans
    apply tsub_sub g ρ1 ρ2 P
    apply tsub_sub g ρ1 ρ2 Q

def tsub_var (f : rmap m1 m2) (g : rmap n1 n2) (ρ1 : pemap Γ f g Δ) (ρ2 : ptmap Γ g Δ) : var Γ x T -> var Δ (f x) (ren_typ g T)
| var.var L Sub =>
  by constructor
     apply ρ1
     assumption
     apply tsub_sub g ρ1 ρ2 Sub

def tsub_term (f : rmap m1 m2) (g : rmap n1 n2) (ρ1 : pemap Γ f g Δ) (ρ2 : ptmap Γ g Δ) : term Γ T -> term Δ (ren_typ g T)
| term.var L => 
  by constructor
     apply tsub_var <;> assumption
| term.app x y =>
  by apply term.app
     · apply (tsub_var f g ρ1 ρ2 x)
     · apply (tsub_var f g ρ1 ρ2 y)
| term.tapp x =>
  by
    conv =>
      pattern (ren_typ g _)
      rw [ren_tsub_comm']
    apply term.tapp
    apply (tsub_var f g ρ1 ρ2 x)
| term.abs x => term.abs (tsub_term (rmap_ext f) g (pemap_ext_var f g ρ1 _) (ptmap_ext_var g ρ2 _) x)
| term.tabs x => term.tabs (tsub_term f (rmap_ext g) (pemap_ext_tvar f g ρ1 _) (ptmap_ext_tvar g ρ2 _) x)
| term.sub t Sub => term.sub (tsub_term f g ρ1 ρ2 t) (tsub_sub g ρ1 ρ2 Sub)
| term.letb t u => term.letb (tsub_term f g ρ1 ρ2 t) (tsub_term (rmap_ext f) g (pemap_ext_var f g ρ1 _) (ptmap_ext_var g ρ2 _) u)

theorem id_rmap_ext {n} :
  rmap_ext (fun x : Fin n => x) = fun x => x :=
  by
    funext x
    cases x using Fin.cases with
    | H0 => simp [rmap_ext]
    | Hs x0 => simp [rmap_ext]

theorem ren_typ_id : ∀ (T : Typ n), ren_typ (fun x => x) T = T
| top => rfl
| tvar X => rfl
| func P Q => by
  simp [ren_typ]
  rw [ren_typ_id (T := P)]
  rw [ren_typ_id (T := Q)]
  simp
| poly P Q =>
  by
    simp [ren_typ]
    rw [ren_typ_id (T := P)]
    simp [id_rmap_ext, ren_typ_id (T := Q)]

def weaken_var_pemap {Γ : Ctx m n} {P} :
  pemap Γ Fin.succ (fun x => x) (extend_var Γ P)
| x , T , L =>
  by 
    simp [ren_typ_id]
    apply LookupVar.lv_there_var
    assumption

def weaken_var_rmap_alt {n : Nat} : rmap n.succ n.succ.succ :=
  fun x => 
    by
      cases x using Fin.cases with
      | H0 => exact 0
      | Hs x0 => exact x0.succ.succ

def weaken_var_pemap_alt {Γ : Ctx m n} {T} {P} :
  pemap (extend_var Γ T) weaken_var_rmap_alt (fun x => x) (extend_var (extend_var Γ P) T) :=
  by
    intro x T L
    cases L
    case lv_here => 
      simp [weaken_var_rmap_alt]
      rw [ren_typ_id]
      apply LookupVar.lv_here
    case lv_there_var L0 =>
      simp [weaken_var_rmap_alt]
      apply LookupVar.lv_there_var
      apply LookupVar.lv_there_var
      rw [ren_typ_id]
      assumption

def weaken_var_ptmap_alt {Γ : Ctx m n} {T} {P} :
  ptmap (extend_var Γ T) (fun x => x) (extend_var (extend_var Γ P) T) :=
  by
    intro X S L
    cases L
    rw [ren_typ_id]
    repeat apply LookupTVar.lt_there_var
    simp
    assumption

def weaken_var_ptmap {Γ : Ctx m n} {P} :
  ptmap Γ (fun x => x) (extend_var Γ P)
| X , S , L =>
  by
    simp
    apply LookupTVar.lt_there_var
    simp [ren_typ_id]
    assumption

def weaken_tvar_pemap {Γ : Ctx m n} {S} :
  pemap Γ (fun x => x) Fin.succ (extend_tvar Γ S)
| x , T , L =>
  by
    simp
    have H : ∀ {n} (T : Typ n),
      ren_typ Fin.succ T = ren_typ (succ_rmap_ext_n 0) T := by
      intro n T
      simp [ren_typ, succ_rmap_ext_n]
    conv =>
      arg 3
      rw [H]
    rw [<- shift_lift_eq_typ]
    apply LookupVar.lv_there_tvar
    assumption

def weaken_tvar_ptmap {Γ : Ctx m n} {S} :
  ptmap Γ Fin.succ (extend_tvar Γ S)
| X , T , L =>
  by
    have H : ∀ {n} (T : Typ n),
      ren_typ Fin.succ T = ren_typ (succ_rmap_ext_n 0) T := by
      intro n T
      simp [ren_typ, succ_rmap_ext_n]
    conv =>
      arg 3
      rw [H]
    rw [<- shift_lift_eq_typ]
    apply LookupTVar.lt_there_tvar
    assumption

def term.copy (t : term Γ T) (h : T = T') : term Γ T' := h ▸ t

def term.copy_weaken_var (t : term (extend_var Γ P) T) (h : P = P') : term (extend_var Γ P') T := h ▸ t 

def term.copy_copy_var (t : term (extend_var Γ P) T) (hp : P = P') (Ht : T = T') : term (extend_var Γ P') T' := Ht ▸ hp ▸ t

def term.copy_weaken_tvar (t : term (extend_tvar Γ S) T) (h : S = S') : term (extend_tvar Γ S') T := h ▸ t

def term.copy_copy_tvar (t : term (extend_tvar Γ S) T) (hs : S = S') (Ht : T = T') : term (extend_tvar Γ S') T' := Ht ▸ hs ▸ t

def subtype.copy_rhs (sub : subtype Γ T U) (h : U = U') : subtype Γ T U' := h ▸ sub

def weaken_var_term' {Γ : Ctx m n} {P} :
  term Γ T ->
  term (extend_var Γ P) (ren_typ (fun x => x) T) :=
  tsub_term Fin.succ (fun x => x) weaken_var_pemap weaken_var_ptmap

def weaken_var_term {Γ : Ctx m n} {P} :
  term Γ T ->
  term (extend_var Γ P) T :=
  fun t => (weaken_var_term' t).copy (ren_typ_id T)

def weaken_var_term_alt' {Γ : Ctx m n} {T P} :
  term (extend_var Γ T) U ->
  term (extend_var (extend_var Γ P) T) (ren_typ (fun x => x) U) :=
  tsub_term weaken_var_rmap_alt (fun x => x) weaken_var_pemap_alt weaken_var_ptmap_alt

def weaken_var_term_alt {Γ : Ctx m n} {T P} :
  term (extend_var Γ T) U ->
  term (extend_var (extend_var Γ P) T) U :=
  fun t => (weaken_var_term_alt' t).copy (ren_typ_id U)

def weaken_var_sub {Γ : Ctx m n} {P} :
  subtype Γ T U ->
  subtype (extend_var Γ P) T U :=
  by
    intro Sub
    have H : ∀ {a} (T : Typ a), T = ren_typ (fun x => x) T := by
      intro T
      simp [ren_typ_id]
    rw [H (T := T)]
    rw [H (T := U)]
    apply (tsub_sub (Γ := Γ) (Δ := extend_var Γ P) (f := Fin.succ) (g := fun x => x))
    exact weaken_var_pemap
    exact weaken_var_ptmap
    assumption

def weaken_tvar_sub {Γ : Ctx m n} {R} :
  subtype Γ T U ->
  subtype (extend_tvar Γ R) (ren_typ Fin.succ T) (ren_typ Fin.succ U) :=
  by
    intro Sub
    apply (tsub_sub (Γ := Γ) (Δ := extend_tvar Γ R) (f := fun x => x) (g := Fin.succ))
    exact weaken_tvar_pemap
    exact weaken_tvar_ptmap
    assumption

def weaken_var_var {Γ : Ctx m n} {P} :
  var Γ x T ->
  var (extend_var Γ P) x.succ T :=
  by
    intro V
    rw [<- ren_typ_id (T := T)]
    apply (tsub_var (Γ := Γ) (Δ := extend_var Γ P) (f := Fin.succ) (g := fun x => x))
    exact weaken_var_pemap
    exact weaken_var_ptmap
    assumption

def subst_ptmap (Γ : Ctx m1 n1) (g : tsmap n1 n2) (Δ : Ctx m2 n2) :=
  ∀ {X S}, LookupTVar Γ X S -> subtype Δ (g X) (tsub_typ g S)

def subst_pemap (Γ : Ctx m1 n1) (f : rmap m1 m2) (g : tsmap n1 n2) (Δ : Ctx m2 n2) :=
  ∀ {x T}, LookupVar Γ x T -> var Δ (f x) (tsub_typ g T)

def subst_ptmap_ext_var (g : tsmap n1 n2) (ρ : subst_ptmap Γ g Δ) T : 
  subst_ptmap (extend_var Γ T) g (extend_var Δ (tsub_typ g T)) :=
  by
    intro X S L
    cases L with
    | lt_there_var L' =>
      apply weaken_var_sub
      apply ρ
      assumption

def subst_pemap_ext_var (f : rmap m1 m2) (g : tsmap n1 n2) (ρ : subst_pemap Γ f g Δ) T :
  subst_pemap (extend_var Γ T) (rmap_ext f) g (extend_var Δ (tsub_typ g T)) :=
  by
    intros x P L
    cases L with
    | lv_here =>
      simp [rmap_ext]
      apply var.var
      apply LookupVar.lv_here
      constructor
    | lv_there_var L' =>
      simp [rmap_ext]
      apply weaken_var_var
      apply ρ
      assumption

def subst_ptmap_ext_tvar (g : tsmap n1 n2) (ρ : subst_ptmap Γ g Δ) S : 
  subst_ptmap (extend_tvar Γ S) (tsmap_ext g) (extend_tvar Δ (tsub_typ g S)) :=
  by
    intro X T L
    cases L with
    | lt_here =>
      conv =>
        pattern (tsmap_ext _ 0)
        simp [tsmap_ext]
      apply subtype.sub_tvar
      rw [tsub_shift_comm_typ]
      apply LookupTVar.lt_here
    | lt_there_tvar L' =>
      conv =>
        pattern (tsmap_ext _ (Fin.succ _))
        simp [tsmap_ext]
      rw [tsub_shift_comm_typ]
      rw [shift_lift_eq_typ']
      unfold lift_typ
      apply weaken_tvar_sub
      apply ρ
      assumption

def weaken_tvar_var {Γ : Ctx m n} {R} :
  var Γ x T ->
  var (extend_tvar Γ R) x (shift_typ T 0) :=
  by
    intro V
    rw [shift_lift_eq_typ']
    apply (tsub_var (Γ := Γ) (Δ := extend_tvar Γ R) (f := fun x => x) (g := Fin.succ))
    exact weaken_tvar_pemap
    exact weaken_tvar_ptmap
    assumption

def subst_pemap_ext_tvar (f : rmap m1 m2) (g : tsmap n1 n2) (ρ : subst_pemap Γ f g Δ) S :
  subst_pemap (extend_tvar Γ S) f (tsmap_ext g) (extend_tvar Δ (tsub_typ g S)) :=
  by
    intro x P L
    cases L with
    | lv_there_tvar L0 =>
      rw [tsub_shift_comm_typ]
      apply weaken_tvar_var
      aesop

lemma open_typ_lifted_eq_tvar (S : Typ n) :
  ∀ m (X : Fin (n + m)),
    (tsmap_ext_n (open_typ_tsmap S) m) (succ_rmap_ext_n m X) = tvar X
| 0 , X =>
  by 
    simp [tsmap_ext_n, succ_rmap_ext_n, open_typ_tsmap]
| Nat.succ n , X =>
  by
    simp [tsmap_ext_n, succ_rmap_ext_n]
    cases X using Fin.cases with
    | H0 => aesop
    | Hs X =>
      simp [rmap_ext]
      unfold tsmap_ext; simp
      rw [open_typ_lifted_eq_tvar (m := n) (X := X)]; aesop

lemma open_typ_lifted_eq (S : Typ n) :
  ∀ m (T : Typ (n + m)),
    tsub_typ (tsmap_ext_n (open_typ_tsmap S) m) (ren_typ (succ_rmap_ext_n m) T) = T
| n , top => rfl
| n , tvar X => by
  simp [tsub_typ]
  rw [open_typ_lifted_eq_tvar]
| n , func P Q =>
  by
    simp [tsub_typ]
    constructor <;> first | rw [open_typ_lifted_eq (T := P)] | rw [open_typ_lifted_eq (T := Q)]
| n , poly P Q =>
  by 
    simp [tsub_typ]
    constructor <;> try rw [open_typ_lifted_eq (T := P)]
    have H := open_typ_lifted_eq (S := S) (m := n.succ) (T := Q)
    simp [tsmap_ext_n, succ_rmap_ext_n] at H
    aesop

lemma open_typ_lifted_eq' :
  ∀ S (T : Typ n),
    tsub_typ (open_typ_tsmap S) (ren_typ Fin.succ T) = T :=
  by
    introv
    have H := open_typ_lifted_eq (S := S) (m := 0) (T := T)
    simp [tsmap_ext_n, succ_rmap_ext_n] at H
    aesop

theorem tsub_tsub_comm_var (g : tsmap n1 n2) (S : Typ n1) :
  ∀ n (X : Fin (n1 + n).succ),
    tsub_typ (tsmap_ext_n' g n) (tsmap_ext_n (open_typ_tsmap S) n X) =
      tsub_typ (tsmap_ext_n (open_typ_tsmap (tsub_typ g S)) n) (tsmap_ext_n' g n.succ X)
| 0 , X =>
  by 
    simp [tsmap_ext_n', tsmap_ext_n]
    cases X using Fin.cases with
    | H0 =>
      simp [tsmap_ext, open_typ_tsmap, tsub_typ]
    | Hs X0 =>
      simp [tsmap_ext]
      conv =>
        pattern (open_typ_tsmap _ (Fin.succ _))
        simp [open_typ_tsmap]
      conv =>
        lhs
        simp [tsub_typ]
      simp [lift_typ]
      rw [open_typ_lifted_eq']
| Nat.succ n , X =>
  by
    simp [tsmap_ext_n', tsmap_ext_n]
    cases X using Fin.cases with
    | H0 => aesop
    | Hs X =>
      conv =>
        pattern (tsmap_ext _ (Fin.succ X))
        simp [tsmap_ext]
      conv =>
        pattern (tsmap_ext _ (Fin.succ _))
        apply congrFun; apply congrFun; simp [tsmap_ext]
      simp
      rw [tsub_lift_comm_typ']
      rw [tsub_lift_comm_typ']
      rw [tsub_tsub_comm_var (n := n) (X := X)]
      simp [tsmap_ext_n']

theorem tsub_tsub_comm_typ (g : tsmap n1 n2) (S : Typ n1) :
  ∀ n (T : Typ (n1 + n).succ),
    tsub_typ (tsmap_ext_n' g n) (tsub_typ (tsmap_ext_n (open_typ_tsmap S) n) T) =
      tsub_typ (tsmap_ext_n (open_typ_tsmap (tsub_typ g S)) n) (tsub_typ (tsmap_ext_n' g n.succ) T)
| n , top => by aesop
| n , tvar X => by simp [tsub_typ]; rw [tsub_tsub_comm_var]
| n , func P Q =>
  by simp [tsub_typ]; constructor; rw [tsub_tsub_comm_typ (T := P)]; rw [tsub_tsub_comm_typ (T := Q)]
| n , poly P Q =>
  by
    simp [tsub_typ]; constructor
    · rw [tsub_tsub_comm_typ g S n P] 
    · have H := tsub_tsub_comm_typ g S n.succ Q 
      simp [tsmap_ext_n', tsmap_ext_n] at H 
      aesop

lemma tsub_open_comm (g : tsmap n1 n2) (S : Typ n1) :
  ∀ T : Typ n1.succ,
    tsub_typ g (open_typ S T) = open_typ (tsub_typ g S) (tsub_typ (tsmap_ext g) T) :=
  by 
    introv
    have H := tsub_tsub_comm_typ g S 0 T
    simp [tsmap_ext_n', tsmap_ext_n] at H
    aesop

def sub_pres_var :
  var Γ x T ->
  subtype Γ T U ->
  var Γ x U
| var.var L Sub1 , Sub2 => var.var L (subtype.sub_trans Sub1 Sub2)

def subst_sub (g : tsmap n1 n2) (ρ1 : subst_pemap Γ f g Δ) (ρ2 : subst_ptmap Γ g Δ) : subtype Γ T U -> subtype Δ (tsub_typ g T) (tsub_typ g U)
| subtype.sub_refl => subtype.sub_refl
| subtype.sub_top => subtype.sub_top
| subtype.sub_func P Q => 
  subtype.sub_func (subst_sub g ρ1 ρ2 P) (subst_sub g ρ1 ρ2 Q)
| subtype.sub_poly P Q =>
  subtype.sub_poly 
    (subst_sub g ρ1 ρ2 P)
    (subst_sub (tsmap_ext g) (subst_pemap_ext_tvar f g ρ1 _) (subst_ptmap_ext_tvar g ρ2 _) Q)
| subtype.sub_tvar L =>
  by
    apply ρ2
    assumption
| subtype.sub_trans P Q =>
  subtype.sub_trans (subst_sub g ρ1 ρ2 P) (subst_sub g ρ1 ρ2 Q)

def subst_var (f : rmap m1 m2) (g : tsmap n1 n2) (ρ1 : subst_pemap Γ f g Δ) (ρ2 : subst_ptmap Γ g Δ) : var Γ x T -> var Δ (f x) (tsub_typ g T)
| var.var L Sub =>
  by
    apply sub_pres_var
    aesop
    apply subst_sub <;> aesop

def subst_term (f : rmap m1 m2) (g : tsmap n1 n2) (ρ1 : subst_pemap Γ f g Δ) (ρ2 : subst_ptmap Γ g Δ) : 
  term Γ T -> 
  term Δ (tsub_typ g T)
| term.var x => by constructor; apply subst_var <;> aesop
| term.app (x := x0) x y =>
  by
    apply term.app
    {
      have H : ∀ n1 n2 (g : tsmap n1 n2) T U, tsub_typ g (func T U) = func (tsub_typ g T) (tsub_typ g U) :=
        by
          intros
          simp [tsub_typ]
      rw [<- H]
      apply subst_var <;> aesop
    }
    {
      apply subst_var <;> aesop
    }
| term.tapp x =>
  by
    rw [tsub_open_comm]
    apply term.tapp
    have H := subst_var f g ρ1 ρ2 x
    aesop
| term.abs t => 
  term.abs (subst_term (rmap_ext f) g (subst_pemap_ext_var f g ρ1 _) (subst_ptmap_ext_var g ρ2 _) t)
| term.tabs t =>
  term.tabs (subst_term f (tsmap_ext g) (subst_pemap_ext_tvar f g ρ1 _) (subst_ptmap_ext_tvar g ρ2 _) t)
| term.sub t Sub =>
  term.sub (subst_term f g ρ1 ρ2 t) (subst_sub g ρ1 ρ2 Sub)
| term.letb t u =>
  term.letb (subst_term f g ρ1 ρ2 t) (subst_term (rmap_ext f) g (subst_pemap_ext_var f g ρ1 _) (subst_ptmap_ext_var g ρ2 _) u)

def id_tsmap (n : Nat) : tsmap n n := fun x => tvar x

lemma id_tsmap_ext_eq : ∀ n,
  tsmap_ext (id_tsmap n) = id_tsmap (n.succ) :=
  by
    introv
    funext x0
    cases x0 using Fin.cases with
    | H0 => rfl
    | Hs x0 => aesop

lemma tsub_id_tsmap : ∀ T, tsub_typ (id_tsmap n) T = T
| top => rfl
| tvar X =>
  by simp [tsub_typ, id_tsmap]
| func P Q =>
  by simp [tsub_typ]; constructor; rw [tsub_id_tsmap (T := P)]; rw [tsub_id_tsmap (T := Q)]
| poly P Q =>
  by
    simp [tsub_typ]; constructor; rw [tsub_id_tsmap (T := P)]
    rw [id_tsmap_ext_eq]
    rw [tsub_id_tsmap (T := Q)]

def lookup_var_succ_inv (Γ : Ctx n m) :
  LookupVar (extend_var Γ P) z Q ->
  z = Fin.succ z0 ->
  LookupVar Γ z0 Q :=
  by
    introv; intro L; intro H
    cases L with
    | lv_here =>
      have H1 := Fin.succ_ne_zero z0
      aesop
    | lv_there_var L0 =>
      aesop

def open_term (t : term (extend_var Γ P) T) (x' : var Γ x0 P) : term Γ T :=
  by
    rw [<- tsub_id_tsmap (T := T)]
    cases x'
    apply subst_term
    case Γ => exact (extend_var Γ P)
    case a => exact t
    case f => 
      unfold rmap; intro z
      cases z using Fin.cases with
      | H0 => exact x0
      | Hs z => exact z
    case ρ2 =>
      unfold subst_ptmap; intro X S LX; rename_i L0
      simp [id_tsmap]
      have H := tsub_id_tsmap (T := S); simp [id_tsmap] at H; rw [H]
      cases LX; rename_i LX
      apply subtype.sub_tvar; aesop
    case ρ1 =>
      unfold subst_pemap; intro z Q Lz
      cases z using Fin.cases with
      | H0 =>
        simp
        rw [tsub_id_tsmap]
        cases Lz with
        | lv_here =>
          constructor <;> aesop
      | Hs z =>
        simp; rw [tsub_id_tsmap]
        constructor; apply lookup_var_succ_inv <;> aesop
        apply subtype.sub_refl

def open_term_typ {Γ : Ctx m n} (S : Typ n) :
  term (extend_tvar Γ S) T ->
  term Γ (open_typ S T) :=
  by
    intro t
    simp [open_typ]
    apply subst_term
    case Γ => exact (extend_tvar Γ S)
    case a => exact t
    case f => exact fun x => x
    case ρ1 =>
      unfold subst_pemap; intro z P Lz
      simp
      cases Lz with
      | lv_there_tvar Lz0 =>
        rw [shift_lift_eq_typ']
        rw [open_typ_lifted_eq']
        apply var.var; aesop; constructor
    case ρ2 =>
      unfold subst_ptmap; intro X P LX
      cases LX with
      | lt_here =>
        rw [shift_lift_eq_typ']
        rw [open_typ_lifted_eq']
        simp [open_typ_tsmap]
        constructor
      | lt_there_tvar LX0 =>
        rw [shift_lift_eq_typ', open_typ_lifted_eq']
        simp [open_typ_tsmap]
        apply subtype.sub_tvar; assumption

@[aesop safe [constructors]]
inductive Value : term Γ T -> Type where
  | v_abs : ∀ t,
    Value (term.abs t)
  | v_tabs : ∀ t, 
    Value (term.tabs t)
  | v_sub :
    Value t ->
    Value (term.sub t sub)

@[aesop safe [constructors]]
inductive Var : ∀ {Γ : Ctx m n} {T : Typ n}, term Γ T -> Type where
  | x_var : ∀ L0, Var (term.var L0)
  | x_sub : ∀ t sub, Var t -> Var (term.sub t sub)

def Var.reify {t : term Γ T} : (x : Var t) -> Σ x, var Γ x T
| x_var L0 => by
  constructor
  assumption
| x_sub t sub x => by
  let IH := Var.reify x
  let ⟨ x0 , (var.var L0 sub0) ⟩ := IH
  constructor
  apply var.var
  exact L0
  apply subtype.sub_trans <;> aesop

structure val (Γ : Ctx m n) (T : Typ n) where
  trm : term Γ T
  isVal : Value trm

inductive store : Ctx m n -> Type where
  | empty : store empty

  | extend : ∀ {Γ},
    store Γ ->
    val Γ T ->
    store (extend_var Γ T)

open store

-- def tsub_term_abs {m n} {f : rmap m1 m2} {g : rmap n1 n2} {ρ1 : pemap Γ f g Δ} {ρ2 : ptmap Γ g Δ} :
--   tsub_term f g ρ1 ρ2 (term.abs t) = term.abs (tsub_term (rmap_ext f) g (pemap_ext_var f g ρ1 _) (ptmap_ext_var g ρ2 _) t) := sorry

lemma id_tsmap_ext {n : Nat} :
  tsmap_ext (n1 := n) (n2 := n) (fun x => tvar x) = fun x => tvar x := by
  funext x
  cases x using Fin.cases <;> simp [tsmap_ext, lift_typ, ren_typ]

lemma tsub_typ_id (P : Typ n) :
  tsub_typ (fun x => tvar x) P = P := by
  induction P <;> simp [tsub_typ]; constructor <;> aesop
  rw [id_tsmap_ext]
  aesop

def narrow_subst_pemap (subp : subtype Γ P' P) :
  subst_pemap (extend_var Γ P) (fun x => x) (fun x => tvar x) (extend_var Γ P') := by
  unfold subst_pemap
  intro x T L
  cases L
  case lv_here =>
    constructor
    apply LookupVar.lv_here
    rw [tsub_typ_id]
    apply weaken_var_sub; aesop
  case lv_there_var L0 =>
    simp
    constructor
    apply LookupVar.lv_there_var
    aesop
    rw [tsub_typ_id]
    constructor

def narrow_tvar_subst_pemap (subp : subtype Γ S' S) :
  subst_pemap (extend_tvar Γ S) (fun x => x) (fun x => tvar x) (extend_tvar Γ S') := by
  unfold subst_pemap
  intro x T L
  cases L
  case lv_there_tvar L0 =>
    simp
    constructor
    apply LookupVar.lv_there_tvar
    aesop
    rw [tsub_typ_id]
    constructor


def narrow_subst_ptmap (subp : subtype Γ P' P) :
  subst_ptmap (extend_var Γ P) (fun x => tvar x) (extend_var Γ P') := by
  unfold subst_ptmap
  intro X S L
  simp
  rw [tsub_typ_id]
  apply subtype.sub_tvar
  cases L
  constructor
  aesop

def narrow_tvar_subst_ptmap (subp : subtype Γ S' S) :
  subst_ptmap (extend_tvar Γ S) (fun x => tvar x) (extend_tvar Γ S') := by
  unfold subst_ptmap
  intro X S L
  simp
  rw [tsub_typ_id]
  cases L with
  | lt_here =>
    apply subtype.sub_trans
    apply subtype.sub_tvar
    apply LookupTVar.lt_here
    repeat rw [shift_lift_eq_typ']
    apply weaken_tvar_sub
    assumption
  | lt_there_tvar L0 =>
    apply subtype.sub_tvar
    apply LookupTVar.lt_there_tvar
    aesop

lemma narrow_var_sub' (subp : subtype Γ P' P) (sub : subtype (extend_var Γ P) T U) :
  subtype (extend_var Γ P') (tsub_typ (fun x => tvar x) T) (tsub_typ (fun x => tvar x) U) :=
  subst_sub 
    (Γ := extend_var Γ P) (Δ := extend_var Γ P')
    (f := fun x => x)
    (fun x => tvar x)
    (narrow_subst_pemap subp)
    (narrow_subst_ptmap subp)
    sub

lemma narrow_var_sub (subp : subtype Γ P' P) (sub : subtype (extend_var Γ P) T U) :
  subtype (extend_var Γ P') T U := by
  rw [<- tsub_typ_id T, <- tsub_typ_id U]
  apply narrow_var_sub' subp sub

lemma narrow_tvar_sub' (subp : subtype Γ S' S) (sub : subtype (extend_tvar Γ S) T U) :
  subtype (extend_tvar Γ S') (tsub_typ (fun x => tvar x) T) (tsub_typ (fun x => tvar x) U) :=
  subst_sub 
    (Γ := extend_tvar Γ S) (Δ := extend_tvar Γ S')
    (f := fun x => x)
    (fun x => tvar x)
    (narrow_tvar_subst_pemap subp)
    (narrow_tvar_subst_ptmap subp)
    sub

lemma narrow_tvar_sub (subp : subtype Γ S' S) (sub : subtype (extend_tvar Γ S) T U) :
  subtype (extend_tvar Γ S') T U := by
  rw [<- tsub_typ_id T, <- tsub_typ_id U]
  apply narrow_tvar_sub' subp sub

lemma narrow_var_term' (subp : subtype Γ P' P) (t : term (extend_var Γ P) T) :
  term (extend_var Γ P') (tsub_typ (fun x => tvar x) T) :=
  subst_term
    (Γ := extend_var Γ P) (Δ := extend_var Γ P')
    (f := fun x => x)
    (fun x => tvar x)
    (narrow_subst_pemap subp)
    (narrow_subst_ptmap subp)
    t

lemma narrow_var_term (subp : subtype Γ P' P) (t : term (extend_var Γ P) T) :
  term (extend_var Γ P') T := by
  rw [<- tsub_typ_id T]
  apply narrow_var_term' subp t

lemma narrow_tvar_term' (subp : subtype Γ S' S) (t : term (extend_tvar Γ S) T) :
  term (extend_tvar Γ S') (tsub_typ (fun x => tvar x) T) :=
  subst_term
    (Γ := extend_tvar Γ S) (Δ := extend_tvar Γ S')
    (f := fun x => x)
    (fun x => tvar x)
    (narrow_tvar_subst_pemap subp)
    (narrow_tvar_subst_ptmap subp)
    t

lemma narrow_tvar_term (subp : subtype Γ S' S) (t : term (extend_tvar Γ S) T) :
  term (extend_tvar Γ S') T := by
  rw [<- tsub_typ_id T]
  apply narrow_tvar_term' subp t

lemma sub_tvar_inv {m n} {Γ : Ctx m n} {S : Typ n} {T : Typ n} {X : Fin n} (sub : subtype Γ S T) :
  T = tvar X ->
  Σ (X' : Fin n), PLift (S = tvar X') := by
  intro Eq
  induction sub <;> try contradiction
  case sub_refl => 
    repeat constructor
    exact Eq
  case sub_trans _ H2 IH1 IH2 =>
    have IH := IH2 Eq
    let ⟨X, Eq⟩ := IH
    let Eq := Eq.down
    have IH := IH1 Eq
    aesop
  case sub_tvar =>
    repeat constructor

lemma sub_fun_inv {m n} {Γ : Ctx m n} {S T U : Typ n} {P : Typ n} (sub : subtype Γ S P) :
  P = func T U ->
  PSum (Σ X : Fin n, PLift (S = tvar X)) (Σ T' U' : Typ n, PProd (S = func T' U') (subtype Γ T T' × subtype Γ U' U)) :=
  by
    intro Eq
    induction sub <;> try contradiction
    case sub_refl => 
      apply PSum.inr; repeat (first | constructor | exact Eq)
    case sub_trans H1 H2 IH1 IH2 =>
      have IH := IH2 Eq
      cases IH with
      | inl IH =>
        let ⟨X, H⟩ := IH
        let Eq := H.down
        have H := sub_tvar_inv H1 Eq
        let ⟨X', Eq⟩ := H
        let Eq := Eq.down
        apply PSum.inl
        repeat constructor
        exact Eq
      | inr IH =>
        let ⟨T', U', IH⟩ := IH
        let ⟨Eq, ⟨sub1, sub2⟩⟩ := IH
        have IH := IH1 Eq
        cases IH with
        | inl IH => aesop
        | inr IH =>
          let ⟨T'', U'', ⟨Eq', ⟨sub1', sub2'⟩⟩⟩ := IH
          apply PSum.inr
          repeat constructor
          exact Eq'
          constructor <;> (apply subtype.sub_trans <;> assumption)
    case sub_tvar =>
      apply PSum.inl
      repeat constructor
    case sub_func =>
      apply PSum.inr
      constructor; constructor; constructor
      exact rfl
      cases Eq
      aesop

lemma sub_poly_inv {Γ : Ctx m n} (sub : subtype Γ S (poly T U)) :
  PSum (Σ X : Fin n, PLift (S = tvar X)) (Σ T' : Typ n, Σ U' : Typ n.succ, PProd (S = poly T' U') (subtype Γ T T' × subtype (extend_tvar Γ T) U' U)) := by
    generalize Eq : poly T U = P at sub
    induction sub <;> try contradiction
    case sub_refl =>
      apply PSum.inr
      constructor; constructor; constructor
      symm; exact Eq
      constructor; constructor; constructor
    case sub_trans h1 h2 ih1 ih2 =>
      have IH := ih2 Eq
      cases IH with
      | inl IH =>
        let ⟨X, H⟩ := IH
        let Eq := H.down
        have H := sub_tvar_inv h1 Eq
        let ⟨X', Eq⟩ := H
        let Eq := Eq.down
        apply PSum.inl
        repeat constructor
        exact Eq
      | inr IH =>
        let ⟨T', U', IH⟩ := IH
        let ⟨Eq, ⟨sub1, sub2⟩⟩ := IH
        symm at Eq
        have IH := ih1 Eq
        cases IH with
        | inl IH => aesop
        | inr IH =>
          let ⟨T'', U'', ⟨Eq', ⟨sub1', sub2'⟩⟩⟩ := IH
          apply PSum.inr
          repeat constructor
          exact Eq'
          constructor
          apply subtype.sub_trans <;> assumption
          apply subtype.sub_trans
          apply narrow_tvar_sub sub1
          exact sub2'
          exact sub2
    case sub_tvar =>
      apply PSum.inl
      repeat constructor
    case sub_poly =>
      apply PSum.inr
      constructor; constructor; constructor
      exact rfl
      cases Eq
      aesop

lemma value_typing {m n} {Γ : Ctx m n} {P : Typ n} {X : Fin n} {t : term Γ P} (v : Value t) :
  P ≠ tvar X := by
  induction v generalizing X
  case v_abs => aesop
  case v_tabs => aesop
  case v_sub sub _ IH =>
    intro Eq
    have H := sub_tvar_inv sub Eq
    cases H; rename_i Neq
    have Neq := Neq.down
    aesop

lemma cf_fun {m n} {Γ : Ctx m n} {T U P : Typ n} {t : term Γ P} (v : Value t) :
  P = func T U ->
  term (extend_var Γ T) U := by
  intro Eq
  induction v generalizing T U <;> try contradiction
  case v_abs t0 =>
    aesop
  case v_sub t0 sub v0 IH =>
    have H := sub_fun_inv sub Eq
    cases H
    case inl H =>
      let ⟨X, Eq⟩ := H
      have Eq := Eq.down
      have H1 := value_typing (t := t0) (X := X) v0
      aesop
    case inr H =>
      let ⟨T', U', ⟨Eq', ⟨sub1, sub2⟩⟩⟩ := H
      have IH := IH Eq'
      apply narrow_var_term sub1
      apply term.sub <;> try assumption
      apply weaken_var_sub
      assumption

lemma cf_fun' {t : term Γ (func T U)} (v : Value t) : term (extend_var Γ T) U :=
  cf_fun v rfl

lemma cf_tfun {t : term Γ (poly T U)} (v : Value t) : term (extend_tvar Γ T) U := by
  generalize Eq : (poly T U) = P at t
  induction v generalizing T U <;> try contradiction
  case v_tabs t0 => aesop
  case v_sub t0 sub v0 IH =>
    rw [<- Eq] at sub
    have H := sub_poly_inv sub
    cases H
    case inl H =>
      let ⟨X, Eq⟩ := H
      have Eq := Eq.down
      have H1 := value_typing (t := t0) (X := X) v0
      aesop
    case inr H =>
      let ⟨T', U', ⟨Eq', ⟨sub1, sub2⟩⟩⟩ := H
      have IH := IH (by symm; assumption)
      apply term.sub
      apply narrow_tvar_term sub1
      assumption; assumption

lemma copy_abs (t : term (extend_var Γ T) U) (h : func T U = func T' U') (ht : T = T') (hu : U = U') :
  (term.abs t).copy h = term.abs (t.copy_copy_var ht hu) :=
  by
    subst_vars
    rfl

lemma copy_tabs (t : term (extend_tvar Γ S) U) (h : poly S U = poly S' U') (hs : S = S') (hu : U = U') :
  (term.tabs t).copy h = term.tabs (t.copy_copy_tvar hs hu) :=
  by
    subst_vars
    rfl

lemma copy_sub (t : term Γ T) (sub : subtype Γ T U) (h : U = U') :
  (term.sub t sub).copy h = term.sub t (sub.copy_rhs h) :=
  by
    subst_vars
    rfl

def weaken_var_value' {P} {t : term Γ T} :
  Value t ->
  Value (weaken_var_term' (P := P) t)
| Value.v_abs t => by
  simp [weaken_var_term', tsub_term]
  constructor
| Value.v_tabs t => by
  simp [weaken_var_term', tsub_term]
  constructor
| Value.v_sub v0 =>
  by 
    simp [weaken_var_term', tsub_term]
    apply Value.v_sub
    have IH := weaken_var_value' (P := P) v0
    aesop

def copy_pres_value {t : term Γ T} (h : T = T') (v : Value t) :
  Value (t.copy h) :=
  by
    subst_vars
    simp [term.copy]
    aesop

def weaken_var_value {P} {t : term Γ T} :
  Value t ->
  Value (weaken_var_term (P := P) t) :=
  by
    intro v
    simp [weaken_var_term]
    apply copy_pres_value
    apply weaken_var_value'
    aesop

def weaken_var_val {P} (t : val Γ T) : val (extend_var Γ P) T :=
  ⟨weaken_var_term t.trm, weaken_var_value t.isVal⟩

def val.sub (t : val Γ T) (sub : subtype Γ T U) : val Γ U :=
  ⟨term.sub t.trm sub, Value.v_sub t.isVal⟩

inductive store_lookup_var : store Γ -> LookupVar Γ x T -> val Γ T -> Prop where
  | slv_here :
    ∀ {m n} {Γ : Ctx m n} {σ : store Γ} {P : Typ n} {t : val Γ P},
      store_lookup_var (extend σ t) LookupVar.lv_here (weaken_var_val t)
  | slv_there :
    ∀ {m n} {Γ : Ctx m n} {σ : store Γ} {T P : Typ n} {t : val Γ P} {t' : val Γ T}
      {x0 : Fin m} {L0 : LookupVar Γ x0 P},
    store_lookup_var σ L0 t ->
    store_lookup_var (extend σ t') (LookupVar.lv_there_var L0) (weaken_var_val t)

inductive store_lookup : store Γ -> var Γ x T -> val Γ T -> Prop where
  | lv_lookup : ∀ {σ : store Γ} {t : val Γ T} {sub : subtype Γ T U},
    store_lookup_var σ L0 t ->
    store_lookup σ (var.var L0 sub) (val.sub t sub)

inductive evconfig : Typ n -> Type where
  | evconfig :
    store Γ ->
    term Γ T ->
    evconfig T

infix:50 " ‖ " => evconfig.evconfig

inductive red : store Γ -> term Γ T -> term Γ T -> Type where
  | red_apply : 
    ∀ {Γ : Ctx m n} {σ : store Γ} {L0 : var Γ x0 (func T U)} 
      {t : val Γ (func T U)} {y : var Γ y0 T},
      store_lookup σ L0 t ->
      red σ (term.app L0 y)
            (open_term (cf_fun' t.isVal) y)

  | red_tapply :
    ∀ {Γ : Ctx m n} {σ : store Γ} {L0 : var Γ x0 (poly S T)} 
      {t : val Γ (poly S T)},
      store_lookup σ L0 t ->
      red σ (term.tapp L0)
            (open_term_typ S (cf_tfun t.isVal))

  | red_rename :
    ∀ {Γ : Ctx m n} {σ : store Γ} {u : term Γ T}
      {t : term (extend_var Γ T) U},
      (x : Var u) ->
      red σ (term.letb u t)
            (open_term t x.reify.snd)

  | red_lift :
    ∀ {Γ : Ctx m n} {σ : store Γ} {v : term Γ T}
      {u u' : term (extend_var Γ T) U},
      (isval : Value v) ->
      red (extend σ (val.mk v isval)) u u' ->
      red σ (term.letb v u)
            (term.letb v u')

  | red_lift_inner :
    ∀ {Γ : Ctx m n} {σ : store Γ} {t : term Γ T}
      {u1 : term (extend_var Γ T) U1}
      {u2 : term (extend_var Γ U1) U2},
      red σ (term.letb (term.letb t u1) u2)
            (term.letb t (term.letb u1 (weaken_var_term_alt u2)))

  | red_let_sub :
    red σ (term.sub (term.letb t u) sub)
          (term.letb t (term.sub u (weaken_var_sub sub)))

  | red_let_ctx :
    red σ t t' ->
    red σ (term.letb t u)
          (term.letb t' u)

  | red_sub : 
    ∀ {Γ : Ctx m n} {σ : store Γ} {t t' : term Γ T}
      {sub : subtype Γ T U},
      red σ t t' ->
      red σ (term.sub t sub)
            (term.sub t' sub)

@[aesop safe [constructors]]
inductive Answer : term Γ T -> Prop where
  | a_var :
    Var t ->
    Answer t

  | a_val :
    Value t ->
    Answer t

  | a_let :
    Value t ->
    Answer u ->
    Answer (term.letb t u)

open Answer

@[aesop safe [constructors]]
inductive Progress : store Γ -> term Γ T -> Prop where
  | p_step : 
    red σ t t' ->
    Progress σ t

  | p_ans :
    Answer t ->
    Progress σ t

open Progress

lemma var_lookup_store : ∀ {σ : store Γ},
  (L : LookupVar Γ x T) ->
  ∃ t, store_lookup_var σ L t
| extend σ t , LookupVar.lv_here => by repeat constructor
| extend σ t' , LookupVar.lv_there_var L0 => 
  by
    rename_i T0 Γ0 x0
    have IH := var_lookup_store (σ := σ) L0
    cases IH; rename_i t0 IH
    constructor
    apply store_lookup_var.slv_there
    aesop

lemma lookup_store : ∀ {σ : store Γ} (L : var Γ x T),
  ∃ t, store_lookup σ L t := by
  intro σ L
  let (var.var L0 sub) := L
  have H := var_lookup_store (σ := σ) L0
  let ⟨ t , H ⟩ := H
  constructor; constructor
  assumption

-- theorem sub_pres_ans {t : term Γ T} (a : Answer t) (sub : subtype Γ T U) :
--   Answer (term.sub t sub) := by
--   cases a with
--   | a_var x =>
--     apply Answer.a_var
--     apply Var.x_sub; assumption
--   | a_val v =>
--     apply Answer.a_val
--     apply Value.v_sub; assumption
--   | a_let v a => sorry

theorem progress : ∀ (σ : store Γ) (t : term Γ T), Progress σ t
| σ , (term.var L0) => by 
  apply p_ans
  apply a_var
  aesop
| σ , (term.sub t sub) =>
  by
    cases progress σ t with
    | p_step r => 
      apply p_step; constructor; aesop
    | p_ans a =>
      cases a with
      | a_var x => apply p_ans; apply a_var; aesop
      | a_val v => apply p_ans; apply a_val; aesop
      | a_let v a =>
        apply p_step
        apply red.red_let_sub
| σ , (term.abs t) => by apply p_ans; apply a_val; aesop
| σ , (term.tabs t) => by apply p_ans; apply a_val; aesop
| σ , (term.app x y) => by
  have H := lookup_store (σ := σ) x
  cases H; rename_i tx H
  let R := red.red_apply (L0 := x) (y := y) H
  apply p_step; assumption
| σ , (term.tapp x) => by
  have H := lookup_store (σ := σ) x
  cases H; rename_i tx H
  let R := red.red_tapply (L0 := x) H
  apply p_step; assumption
| σ , (term.letb t u) => by
  have IH := progress σ t
  cases IH with
  | p_step r => apply p_step; apply red.red_let_ctx; assumption
  | p_ans a =>
    cases a with
    | a_var x =>
      apply p_step
      apply red.red_rename; assumption
    | a_val v =>
      have IH := progress (extend σ (val.mk t v)) u
      cases IH with
      | p_step r =>
        apply p_step
        apply red.red_lift; assumption
      | p_ans a1 =>
        apply p_ans
        apply a_let <;> assumption
    | a_let v a =>
      apply p_step
      apply red.red_lift_inner
