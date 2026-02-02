import Mathlib.Data.Fin.Basic
import Capless.Reduction
import Capless.Narrowing.TypedCont
import Capless.Inversion.Lookup
import Capless.Inversion.Typing
import Capless.Weakening.IsValue
import Capless.WellScoped.Basic

/-!
# Progress Theorem

This module proves that a well-typed term is either an answer (in which case the reduction halts), or can be further reduced. Theorem `progress` is the main result.
-/

namespace Capless

theorem Store.lookup_exists {σ : Store n m k} {x : Fin n} :
  (∃ v, Store.Bound σ x v ∧ v.IsValue) ∨ (∃ c S, Store.LBound σ x c S) := by
  induction σ
  case empty => exact Fin.elim0 x
  case val =>
    cases x using Fin.cases
    case zero =>
      apply Or.inl
      constructor; constructor
      { constructor }
      { apply Term.IsValue.weaken; trivial }
    case succ x0 =>
      rename_i ih
      have ih := ih (x := x0)
      cases ih
      case inl ih =>
        let ⟨v, hb, hv⟩ := ih
        apply Or.inl
        constructor; constructor
        { constructor; trivial }
        { apply Term.IsValue.weaken; trivial }
      case inr ih =>
        apply Or.inr
        have ⟨c, S, ih⟩ := ih
        constructor
        constructor
        constructor; easy
  case tval ih =>
    have ih := ih (x := x)
    cases ih
    case inl ih =>
      have ⟨v, hb, hv⟩ := ih
      apply Or.inl
      constructor; constructor
      { constructor; trivial }
      { apply Term.IsValue.tweaken; trivial }
    case inr ih =>
      apply Or.inr
      have ⟨c, S, ih⟩ := ih
      constructor
      constructor
      constructor; easy
  case cval ih =>
    have ih := ih (x := x)
    cases ih
    case inl ih =>
      have ⟨v, hb, hv⟩ := ih
      apply Or.inl
      constructor; constructor
      { constructor; trivial }
      { apply Term.IsValue.cweaken; trivial }
    case inr ih =>
      apply Or.inr
      have ⟨c, S, ih⟩ := ih
      constructor
      constructor
      constructor; easy
  case label ih =>
    cases x using Fin.cases
    case zero =>
      apply Or.inr
      constructor
      constructor
      constructor
    case succ x0 =>
      have ih := ih (x := x0)
      cases ih
      case inl ih =>
        have ⟨v, hb, hv⟩ := ih
        apply Or.inl
        constructor; constructor
        { constructor; trivial }
        { apply Term.IsValue.weaken; trivial }
      case inr ih =>
        apply Or.inr
        have ⟨c, S, ih⟩ := ih
        constructor
        constructor
        constructor; easy

theorem Store.val_lookup_exists {σ : Store n m k} {x : Fin n}
  (hs : TypedStore σ Γ) (hx : Typed Γ (Term.var x) (EType.type T) Cx)
  (hvt : T.IsValue) :
  ∃ v, Store.Bound σ x v ∧ v.IsValue := by
  have hg := TypedStore.is_tight hs
  have h := Store.lookup_exists (σ := σ) (x := x)
  cases h
  case inl h => easy
  case inr h =>
    have ⟨c, S, hl⟩ := h
    have hb := Store.bound_label hl hs
    have ⟨c0, S0, hb0, hsub⟩ := Typed.label_inv hx hb
    have ⟨_, _⟩ := Context.lbound_inj hb hb0
    subst_vars
    cases hvt
    case capt hvt =>
      cases hsub; rename_i hsub
      cases hvt
      case xforall =>
        have ⟨_, _, hd1⟩ := SSubtyp.dealias_right_forall hsub hg (by constructor)
        cases hd1
      case tforall =>
        have ⟨_, _, hd1⟩ := SSubtyp.dealias_right_tforall hsub hg (by constructor)
        cases hd1
      case cforall =>
        have ⟨_, _, hd1⟩ := SSubtyp.dealias_right_cforall hsub hg (by constructor)
        cases hd1
      case box =>
        have ⟨_, hd1⟩ := SSubtyp.dealias_right_boxed hsub hg (by constructor)
        cases hd1

theorem Store.value_typing_label_absurd'
  (hg : Γ.IsTight)
  (he : E0 = EType.type (S0^C))
  (hd : SType.Dealias Γ S0 (Label[S]))
  (ht : Typed Γ v E0 Cv)
  (hv : v.IsValue) : False := by
  induction ht <;> try (solve | cases hv | cases he; try cases hd)
  case sub ih =>
    cases he
    rename_i hsub
    cases hsub; rename_i hsub
    cases hsub; rename_i hsub
    have hd0 := SSubtyp.dealias_right_label hsub hg hd
    aesop

theorem Store.value_typing_label_absurd
  (hg : Γ.IsTight)
  (ht : Typed Γ v (EType.type (Label[S]^C)) Cv)
  (hv : v.IsValue) : False :=
  Store.value_typing_label_absurd' hg (by rfl) (by constructor) ht hv

theorem Store.label_lookup_exists {σ : Store n m k} {x : Fin n}
  (hs : TypedStore σ Γ)
  (hx : Typed Γ (Term.var x) (EType.type (Label[S]^C)) Cx) :
  ∃ c0 S0, Store.LBound σ x c0 S0 := by
  have hg := TypedStore.is_tight hs
  have h := Store.lookup_exists (σ := σ) (x := x)
  cases h
  case inr => easy
  case inl h =>
    have ⟨v, hl, hv⟩ := h
    have ⟨Cv, Cv0, htv⟩ := Store.lookup_inv_typing_alt hl hs hx
    exfalso
    apply Store.value_typing_label_absurd hg htv hv

@[aesop unsafe [constructors 50%]]
inductive Progress : State n m k -> Prop where
| halt_var :
  Progress ⟨σ, Cont.none, Term.var x⟩
| halt_value {t : Term n m k} :
  t.IsValue ->
  Progress ⟨σ, Cont.none, t⟩
| step :
  Reduce state state' ->
  Progress state

-- Needed for the `aesop` searches in `progress` to terminate.
set_option maxHeartbeats 314159265358

theorem progress
  (ht : TypedState state Γ E Rt) :
  Progress state := by
  cases ht
  case mk hs ht hc hr hsc =>
    induction ht
    case var =>
      cases hc <;> aesop
    case label =>
      cases hc <;> aesop
    case pack =>
      cases hc <;> aesop
    case sub hsubcapt hsub ih _ _ _ =>
      have ⟨R', _, h⟩ := hr.subcapt hsubcapt
      apply ih
      . easy
      . apply! TypedCont.narrow (TypedCont.cin_narrow hc _) _
      . apply h
      . apply! WellScoped.subset
    case abs => cases hc <;> aesop
    case tabs => cases hc <;> aesop
    case cabs => cases hc <;> aesop
    case app =>
      rename_i x _ _ _ _ hx _ _ _ σ _ _
      have hg := TypedStore.is_tight hs
      have ⟨v0, hb0, hv0⟩ := Store.val_lookup_exists (σ := σ) (x := x) hs hx (by aesop)
      have ⟨Cv, Cv0, htv⟩ := Store.lookup_inv_typing_alt hb0 hs hx
      have ⟨U0, t0, he⟩ := Typed.forall_inv hg hv0 htv
      aesop
    case tapp x _ _ _ hx _ σ _ _ =>
      have hg := TypedStore.is_tight hs
      have ⟨v0, hb0, hv0⟩ := Store.val_lookup_exists (σ := σ) (x := x) hs hx (by aesop)
      have ⟨Cv, Cv0, htv⟩ := Store.lookup_inv_typing_alt hb0 hs hx
      have ⟨U0, t0, he⟩ := Typed.tforall_inv hg hv0 htv
      aesop
    case capp x _ _ _ hx _ σ _ _ =>
      have hg := TypedStore.is_tight hs
      have ⟨v0, hb0, hv0⟩ := Store.val_lookup_exists (σ := σ) (x := x) hs hx (by aesop)
      have ⟨Cv, Ct0, htv⟩ := Store.lookup_inv_typing_alt hb0 hs hx
      have ⟨t0, he⟩ := Typed.cforall_inv hg hv0 htv
      aesop
    case letin => aesop
    case letex => aesop
    case bindt => aesop
    case bindc => aesop
    case invoke hx hy _ _ σ cont Ct =>
      cases hr; rename_i hr _
      cases hsc; rename_i hsc _
      have hg := TypedStore.is_tight hs
      have ⟨c0, S0, hl⟩ := Store.label_lookup_exists hs hx
      have hl := Store.bound_label hl hs
      have ⟨_, hsl⟩ := hr.label_inv hsc hl
      have ⟨handler, tail, hsi⟩ := hsl.has_intercept (L:=.classifier c0)
      cases handler <;> aesop
    case boundary => aesop
    case intercept => aesop

end Capless
