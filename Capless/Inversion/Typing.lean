import Capless.Typing
import Capless.Subtyping.Basic
import Capless.Inversion.Subtyping
namespace Capless

theorem Typed.app_inv'
  (he : t0 = Term.app x y)
  (h : Typed Γ t0 E) :
  ∃ T Cf F E0, Typed Γ (Term.var x) (EType.type (CType.capt Cf (SType.forall T F)))
    ∧ Typed Γ (Term.var y) (EType.type T)
    ∧ E0 = F.open y
    ∧ ESubtyp Γ E0 E := by
    induction h <;> try (solve | cases he)
    case app x C T F y h1 h2 _ _ =>
      cases he
      exists T, C, F, (F.open y)
      repeat (constructor; trivial)
      apply ESubtyp.refl
    case sub hsub ih =>
      have ih := ih he
      have ⟨T0, Cf0, E0, F0, hx0, hy0, he0, hs0⟩ := ih
      exists T0, Cf0, E0, F0
      repeat (constructor; trivial)
      apply ESubtyp.trans
      { trivial }
      { trivial }

theorem Typed.app_inv
  (h : Typed Γ (Term.app x y) E) :
  ∃ T Cf F E0, Typed Γ (Term.var x) (EType.type (CType.capt Cf (SType.forall T F)))
    ∧ Typed Γ (Term.var y) (EType.type T)
    ∧ E0 = F.open y
    ∧ ESubtyp Γ E0 E :=
  Typed.app_inv' rfl h

theorem Typed.var_inv'
  (he1 : t0 = Term.var x)
  (he2 : E0 = EType.type T)
  (h : Typed Γ t0 E0) :
  ∃ T0, Γ.Bound x T0 ∧ CSubtyp Γ T0 T := by
  induction h <;> try (solve | cases he1 | cases he2)
  case var T0 hb =>
    cases he1; cases he2
    apply Exists.intro T0
    constructor
    { trivial }
    { apply CSubtyp.refl }
  case sub hs ih =>
    have h := ESubtyp.sub_type_inv' he2 hs
    have ⟨T1, he, hs1⟩ := h
    have ih := ih he1 he
    have ⟨T0, hb, hs0⟩ := ih
    apply Exists.intro T0
    constructor
    { trivial }
    { apply CSubtyp.trans <;> trivial }

theorem Typed.var_inv
  (h : Typed Γ (Term.var x) (EType.type T)) :
  ∃ T0, Γ.Bound x T0 ∧ CSubtyp Γ T0 T := by
  apply Typed.var_inv' rfl rfl h

theorem Typed.canonical_form_lam'
  (he1 : t0 = Term.lam T t) (he2 : E0 = EType.type (CType.capt Cf (SType.forall T' E)))
  (h : Typed Γ t0 E0) :
  CSubtyp Γ T' T ∧
  Typed (Γ.var T') t E := by
  induction h <;> try (solve | cases he1 | cases he2)
  case abs =>
    cases he1; cases he2
    constructor
    { apply CSubtyp.refl }
    { trivial }
  case sub hs ih => sorry

theorem Typed.canonical_form_lam
  (h : Typed Γ (Term.lam T t) (EType.type (CType.capt Cf (SType.forall T' E)))) :
  CSubtyp Γ T' T ∧
  Typed (Γ.var T') t E := sorry

end Capless
