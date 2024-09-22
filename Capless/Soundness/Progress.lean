import Mathlib.Data.Fin.Basic
import Capless.Reduction
import Capless.Narrowing.TypedCont
import Capless.Inversion.Lookup
import Capless.Inversion.Typing
import Capless.Weakening.IsValue
namespace Capless

theorem Store.lookup_exists {σ : Store n m k} {x : Fin n} :
  ∃ v, Store.Bound σ x v ∧ v.IsValue := by
  induction σ
  case empty => exact Fin.elim0 x
  case val =>
    cases x using Fin.cases
    case zero =>
      constructor; constructor
      { constructor }
      { apply Term.IsValue.weaken; trivial }
    case succ x0 =>
      rename_i ih
      have ⟨v0, hb0, hv0⟩ := ih (x := x0)
      constructor; constructor
      { constructor; trivial }
      { apply Term.IsValue.weaken; trivial }
  case tval ih =>
    have ⟨v, hb, hv⟩ := ih (x := x)
    constructor; constructor
    { constructor; trivial }
    { apply Term.IsValue.tweaken; trivial }
  case cval ih =>
    have ⟨v, hb, hv⟩ := ih (x := x)
    constructor; constructor
    { constructor; trivial }
    { apply Term.IsValue.cweaken; trivial }

inductive Progress : State n m k -> Prop where
| step :
  Reduce state state' ->
  Progress state
| halt_value {t : Term n m k} :
  t.IsValue ->
  Progress ⟨σ, Cont.none, t⟩
| halt_var :
  Progress ⟨σ, Cont.none, Term.var x⟩

theorem progress
  (ht : TypedState state Γ E) :
  Progress state := by
  cases ht
  case mk hs ht hc =>
    induction ht
    case var =>
      cases hc
      case none => apply Progress.halt_var
      case cons =>
        apply Progress.step
        apply Reduce.rename
    case pack =>
      cases hc
      case none => apply Progress.halt_value; constructor
      case conse =>
        apply Progress.step
        apply Reduce.lift_ex
    case sub hsub ih _ _ =>
      apply ih <;> try trivial
      apply! TypedCont.narrow
    case abs =>
      cases hc
      case none => apply Progress.halt_value; constructor
      case cons =>
        apply Progress.step
        apply Reduce.lift
        constructor
    case tabs =>
      cases hc
      case none => apply Progress.halt_value; constructor
      case cons =>
        apply Progress.step
        apply Reduce.lift
        constructor
    case cabs =>
      cases hc
      case none => apply Progress.halt_value; constructor
      case cons =>
        apply Progress.step
        apply Reduce.lift
        constructor
    case app =>
      rename_i x _ _ _ _ _ hx _ _ _ σ _
      have hg := TypedStore.is_tight hs
      have ⟨v0, hb0, hv0⟩ := Store.lookup_exists (σ := σ) (x := x)
      have ⟨Cv, Cv0, htv⟩ := Store.lookup_inv_typing hb0 hs hx
      have ⟨U0, t0, he⟩ := Typed.forall_inv hg hv0 htv
      subst he
      apply Progress.step
      apply Reduce.apply
      trivial
    case tapp x _ _ _ _ hx _ σ _ =>
      have hg := TypedStore.is_tight hs
      have ⟨v0, hb0, hv0⟩ := Store.lookup_exists (σ := σ) (x := x)
      have ⟨Cv, Cv0, htv⟩ := Store.lookup_inv_typing hb0 hs hx
      have ⟨U0, t0, he⟩ := Typed.tforall_inv hg hv0 htv
      subst he
      apply Progress.step
      apply Reduce.tapply
      trivial
    case capp x _ _ _ _ hx _ σ _ =>
      have hg := TypedStore.is_tight hs
      have ⟨v0, hb0, hv0⟩ := Store.lookup_exists (σ := σ) (x := x)
      have ⟨Cv, Ct0, htv⟩ := Store.lookup_inv_typing hb0 hs hx
      have ⟨t0, he⟩ := Typed.cforall_inv hg hv0 htv
      subst he
      apply Progress.step
      apply Reduce.capply
      trivial
    case box =>
      cases hc
      case none => apply Progress.halt_value; constructor
      case cons =>
        apply Progress.step
        apply Reduce.lift
        constructor
    case unbox x _ _ _ hx _ σ _ =>
      have hg := TypedStore.is_tight hs
      have ⟨v0, hb0, hv0⟩ := Store.lookup_exists (σ := σ) (x := x)
      have ⟨Cv, Cv0, htv⟩ := Store.lookup_inv_typing hb0 hs hx
      have ⟨t0, he⟩ := Typed.boxed_inv hg hv0 htv
      subst he
      apply Progress.step
      apply Reduce.unbox
      trivial
    case letin =>
      apply Progress.step
      apply Reduce.push
    case letex =>
      apply Progress.step
      apply Reduce.push_ex
    case bindt =>
      apply Progress.step
      apply Reduce.tlift
    case bindc =>
      apply Progress.step
      apply Reduce.clift

end Capless
