import Mathlib.Data.Fin.Basic
import Capless.Reduction
import Capless.Narrowing.TypedCont
import Capless.Inversion.Lookup
import Capless.Inversion.Typing
import Capless.Weakening.IsValue
import Capless.WellScoped.Basic
namespace Capless

theorem Store.lookup_exists {σ : Store n m k} {x : Fin n} :
  (∃ v, Store.Bound σ x v ∧ v.IsValue) ∨ (∃ S, Store.LBound σ x S) := by
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
        have ⟨S, ih⟩ := ih
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
      have ⟨S, ih⟩ := ih
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
      have ⟨S, ih⟩ := ih
      constructor
      constructor; easy
  case label ih =>
    cases x using Fin.cases
    case zero =>
      apply Or.inr
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
        have ⟨S, ih⟩ := ih
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
    have ⟨S, hl⟩ := h
    have hb := Store.bound_label hl hs
    have ⟨S0, hb0, hsub⟩ := Typed.label_inv hx hb
    have h := Context.lbound_inj hb hb0
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
        have ⟨_, hd1⟩ := SSubtyp.dealias_right_cforall hsub hg (by constructor)
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
  ∃ S0, Store.LBound σ x S0 := by
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

theorem progress
  (ht : TypedState state Γ E) :
  Progress state := by
  cases ht
  case mk hs ht hsc hc =>
    induction ht
    case var =>
      cases hc <;> aesop
    case label =>
      cases hc <;> aesop
    case pack =>
      cases hc <;> aesop
    case sub hsub ih _ _ _ =>
      apply ih <;> try easy
      apply WellScoped.subcapt; easy; easy
      apply! TypedCont.narrow
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
    case box => cases hc <;> aesop
    case unbox x _ _ hx _ σ _ _ =>
      have hg := TypedStore.is_tight hs
      have ⟨v0, hb0, hv0⟩ := Store.val_lookup_exists (σ := σ) (x := x) hs hx (by aesop)
      have ⟨Cv, Cv0, htv⟩ := Store.lookup_inv_typing_alt hb0 hs hx
      have ⟨t0, he⟩ := Typed.boxed_inv hg hv0 htv
      aesop
    case letin => aesop
    case letex => aesop
    case bindt => aesop
    case bindc => aesop
    case invoke hx hy _ _ σ cont Ct =>
      cases hsc; rename_i hsc _
      have hg := TypedStore.is_tight hs
      have ⟨S0, hl⟩ := Store.label_lookup_exists hs hx
      have hl := Store.bound_label hl hs
      have ⟨_, hsl⟩ := WellScoped.label_inv hsc hl
      aesop
    case boundary => aesop

end Capless
