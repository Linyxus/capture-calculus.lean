import Mathlib.Data.Fin.Basic
import CC.Basic
import CC.CaptureSet
import CC.Type
import CC.Context
import CC.TypeMap
import CC.Typed
import CC.Subcapt
import CC.Subcapt.Basic
import CC.Subtype.Basic

namespace CC

lemma LetC.subst_hole
  (h : LetC t Ct u C) :
  ∃ C', LetC t' Ct' u C' := by
  cases h with
  | normal =>
    apply Exists.intro
    constructor; aesop
  | gc =>
    apply Exists.intro
    apply normal
    constructor; aesop

lemma LetC.subst_hole1
  (h : LetC t Ct Cu C) :
  ∃ C', LetC t' Ct' (CaptureSet.weaken_var1 Cu) C' := by
  cases h with
  | normal =>
    apply Exists.intro
    constructor
    unfold CaptureSet.weaken_var1
    apply DropBinder.rename; aesop
  | gc =>
    apply Exists.intro
    apply normal
    constructor
    unfold CaptureSet.weaken_var1
    apply DropBinderFree.rename; aesop

theorem Typed.var_inv_subcapt' : 
  t0 = Term.var x ->
  T0 = CType.capt C S ->
  Typed Γ t0 Cx T0 ->
  Subcapt Γ {x} C := by
  intro eq1 eq2 h
  induction h 
  case var =>
    cases eq1
    cases eq2
    apply Subcapt.refl
  case sub ih =>
    rename_i T T' _ _
    cases T
    have ih := ih eq1 rfl
    rename_i hsub _
    cases hsub
    rename_i hsub _
    cases eq2
    apply Subcapt.sc_trans
    exact ih
    aesop
  all_goals cases eq1

theorem Typed.var_inv_subcapt :
  Typed Γ (Term.var x) Cx (CType.capt C S) ->
  Subcapt Γ {x} C := by
  apply Typed.var_inv_subcapt' <;> aesop

theorem Typed.app_inv' :
  t0 = Term.app x y ->
  Typed Γ t0 C0 U ->
  ∃ Cx Cy Cf D T U0, Typed Γ (Term.var x) Cx (CType.capt Cf (PType.arr D T U0)) ∧ 
    Typed Γ (Term.var y) Cy T ∧
    Subtype Γ (U0.open_var y) U := by
  intro heq h
  induction h <;> try (solve | cases heq)
  case app h1 h2 _ _ =>
    cases heq
    repeat (apply Exists.intro)
    apply And.intro
    exact h1
    apply And.intro
    exact h2
    apply Subtype.refl
  case sub h hsub ih =>
    have ih' := ih heq
    let ⟨Cx0, Cy0, Cf0, D0, T0, U0, hx, hy, heq0⟩ := ih'
    clear ih
    subst_vars
    repeat apply Exists.intro
    apply And.intro
    exact hx
    apply And.intro
    exact hy
    apply Subtype.trans <;> aesop

theorem Typed.app_inv :
  Typed Γ (Term.app x y) C0 U ->
  ∃ Cx Cy Cf D T U0, Typed Γ (Term.var x) Cx (CType.capt Cf (PType.arr D T U0)) ∧ 
    Typed Γ (Term.var y) Cy T ∧
    Subtype Γ (U0.open_var y) U := by
  apply Typed.app_inv'
  rfl

theorem Typed.tapp_inv' :
  t0 = Term.tapp x S ->
  Typed Γ t0 C0 U ->
  ∃ Cx Cf U0,
    Typed Γ (Term.var x) Cx (CType.capt Cf (PType.tarr S U0)) ∧
    Subtype Γ (U0.open_tvar S) U := by
    intros he h
    induction h <;> try (solve | cases he)
    case tapp =>
      cases he
      repeat apply Exists.intro
      repeat apply And.intro
      assumption
      apply Subtype.refl
    case sub hsub ih =>
      have ih := ih he
      let ⟨Cx, Cf, U0, ht, hs⟩ := ih
      repeat apply Exists.intro; repeat apply And.intro
      trivial
      apply Subtype.trans <;> trivial

theorem Typed.tapp_inv :
  Typed Γ (Term.tapp x S) C0 U ->
  ∃ Cx Cf U0,
    Typed Γ (Term.var x) Cx (CType.capt Cf (PType.tarr S U0)) ∧
    Subtype Γ (U0.open_tvar S) U := by
  apply Typed.tapp_inv'; aesop

theorem Typed.unbox_inv' :
  t0 = Term.unbox C x ->
  Typed Γ t0 C0 U ->
  ∃ Cx Cf,
    Typed Γ (Term.var x) Cx (CType.capt Cf (PType.boxed U)) := by
    intros he h
    induction h <;> try (solve | cases he)
    case unbox => aesop
    case sub ih =>
      have ih' := ih he
      let ⟨Cx, Cf, hx⟩ := ih'
      repeat apply Exists.intro
      apply Typed.sub
      exact hx
      constructor
      apply Subcapt.refl
      apply SubtypeP.boxed
      trivial

theorem Typed.unbox_inv :
  Typed Γ (Term.unbox C x) C0 U ->
  ∃ Cx Cf,
    Typed Γ (Term.var x) Cx (CType.capt Cf (PType.boxed U)) := by apply Typed.unbox_inv'; aesop

def LetHole 
  (Γ : Ctx n m) 
  (u : Term n.succ m)
  (T : CType n m) (U : CType n m) : Prop :=
  ∀ Ct' t',
    Typed Γ t' Ct' T ->
    ∃ C', Typed Γ (Term.letval t' u) C' U

def LetHole1
  (Γ : Ctx n m) 
  (u : Term n.succ m)
  (T : CType n m) (U : CType n m) : Prop :=
  ∀ Ct' t' P,
    Typed (Ctx.extend_var Γ {} P) t' Ct' T.weaken_var ->
    ∃ C', Typed (Ctx.extend_var Γ {} P) (Term.letval t' u.weaken_var1) C' U.weaken_var

theorem Typed.let_inv' :
  t0 = Term.letval t u ->
  Typed Γ t0 C0 U ->
  ∃ Ct Cu T U0 U1,
    Typed Γ t Ct T ∧
    Typed (Ctx.extend_var Γ {} T) u Cu U0 ∧
    U0 = CType.weaken_var U1 ∧
    Subtype Γ U1 U ∧
    LetHole Γ u T U ∧
    LetHole1 Γ u T U := by
  intro he h
  induction h <;> try (solve | cases he)
  case letval =>
    cases he
    repeat apply Exists.intro
    repeat (apply And.intro; (first | assumption | apply Subtype.refl))
    apply And.intro
    · intros Ct' t' Ht'
      rename_i hc _ _
      have hc' := hc.subst_hole (t' := t') (Ct' := Ct')
      cases hc'; rename_i hc'
      constructor
      apply Typed.letval <;> try assumption
    · intros Ct' t' P Ht'
      rename_i hc _ _
      have hc' := LetC.subst_hole1 (t' := t') (Ct' := Ct') hc; cases hc'
      apply Exists.intro
      apply Typed.letval
      exact Ht'
      rw [<- SepDegree.empty_weaken_var]
      apply Typed.weaken_var1
      trivial
      subst_vars
      simp [CType.weaken_var1_weaken_var]
      trivial
  case sub hsub ih =>
    let ⟨Ct, Cu, T, U0, U1, h1, h2, heq, hs, hh, hh1⟩ := ih he
    repeat apply Exists.intro
    repeat (apply And.intro; assumption)
    apply And.intro
    apply Subtype.trans <;> trivial
    apply And.intro
    · unfold LetHole at *
      intros Ct' t' Ht'
      have ⟨C', h0⟩ := hh Ct' t' Ht'
      apply Exists.intro
      apply Typed.sub <;> trivial
    · intros Ct' t' P Ht'
      have ⟨C', h0⟩ := hh1 Ct' t' P Ht'
      apply Exists.intro
      apply Typed.sub
      · trivial
      · apply Subtype.weaken_var; trivial

theorem Typed.let_inv :
  Typed Γ (Term.letval t u) C0 U ->
  ∃ Ct Cu T U0 U1,
    Typed Γ t Ct T ∧
    Typed (Ctx.extend_var Γ {} T) u Cu U0 ∧
    U0 = CType.weaken_var U1 ∧
    Subtype Γ U1 U ∧
    LetHole Γ u T U ∧ LetHole1 Γ u T U := by
  intro h
  apply let_inv' <;> trivial

theorem Typed.var_typing_bound' :
  t0 = Term.var x ->
  T0 = CType.capt C S ->
  Typed Γ t0 Cx T0 ->
  ∃ D C' S', BoundVar Γ x D (CType.capt C' S') ∧ SubtypeP Γ S' S := by
  intro he1 he2 h
  induction h <;> try (solve | cases he1 | cases he2)
  case var hb =>
    cases he1; cases he2
    repeat (apply Exists.intro)
    apply And.intro
    exact hb
    apply SubtypeP.refl
  case sub T _ h hsub ih =>
    cases he1; cases he2
    cases T
    have ih := ih rfl rfl
    let ⟨D, C', S, hb, hsub0⟩ := ih
    repeat (apply Exists.intro)
    apply And.intro
    exact hb
    cases hsub
    apply SubtypeP.trans <;> trivial

theorem Typed.var_typing_bound :
  Typed Γ (Term.var x) Cx (CType.capt C S) ->
  ∃ D C' S', BoundVar Γ x D (CType.capt C' S') ∧ SubtypeP Γ S' S := by 
  apply Typed.var_typing_bound' <;> aesop

theorem Typed.var_typing_captures'
  (he : t0 = Term.var x)
  (h : Typed Γ t0 Cx T) :
  Cx = {x} := by
  induction h <;> try (solve | cases he | aesop)

theorem Typed.var_typing_captures
  (h : Typed Γ (Term.var x) Cx T) :
  Cx = {x} := by
  apply Typed.var_typing_captures' <;> trivial
