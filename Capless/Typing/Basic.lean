import Capless.Typing
import Capless.Subcapturing
import Capless.Subcapturing.Basic
import Capless.Subtyping.Basic
namespace Capless

theorem Typing.inv_subcapt'
  (he1 : t0 = Term.var x) (he2 : E0 = EType.type (CType.capt C S))
  (h : Typed Γ t0 E0 C0) :
  Subcapt Γ {x=x} C := by
  induction h <;> try (solve | cases he1 | cases he2)
  case var =>
    cases he1; cases he2
    apply Subcapt.refl
  case sub hsub ih =>
    subst he1 he2
    have h := ESubtyp.type_inv_subcapt hsub
    let ⟨C0, S0, he, hs⟩ := h
    subst he
    have ih := ih rfl rfl
    apply Subcapt.trans; trivial; trivial

theorem Typing.inv_subcapt
  (h : Typed Γ (Term.var x) (EType.type (CType.capt C S)) C0) :
  Subcapt Γ {x=x} C :=
  Typing.inv_subcapt' rfl rfl h

theorem Typed.bound_typing
  (hb : Context.Bound Γ x T) :
  Typed Γ (Term.var x) (EType.type T) {} := by
  cases T
  apply Typed.sub
  apply Typed.var hb
  apply Subcapt.refl
  constructor
  constructor
  apply Subcapt.var; trivial
  apply SSubtyp.refl

theorem Typed.precise_capture'
  (he1 : t0 = Term.var x)
  (he2 : E0 = EType.type (CType.capt C S))
  (h : Typed Γ t0 E0 C0) :
  Typed Γ (Term.var x) (EType.type (CType.capt {x=x} S)) {} := by
  induction h <;> try (solve | cases he1 | cases he2)
  case var => cases he1; cases he2; apply Typed.var; trivial
  case sub hsub ih =>
    subst_vars
    cases hsub
    rename_i hsub
    cases hsub
    rename_i hsc hss
    have ih := ih rfl rfl
    apply Typed.sub
    { exact ih }
    { apply Subcapt.refl }
    { constructor
      constructor
      apply Subcapt.refl
      trivial }

theorem Typed.precise_capture
  (h : Typed Γ (Term.var x) (EType.type (CType.capt C S)) C0) :
  Typed Γ (Term.var x) (EType.type (CType.capt {x=x} S)) {} :=
  Typed.precise_capture' rfl rfl h

theorem Typed.precise_cv'
  (he : t0 = Term.var x)
  (h : Typed Γ t0 E C0) :
  Typed Γ (Term.var x) E {} := by
  induction h <;> try (solve | cases he)
  case var => cases he; apply Typed.var; trivial
  case sub ih =>
    apply Typed.sub
    { apply! ih }
    { apply Subcapt.refl }
    { trivial }

theorem Typed.precise_cv
  (h : Typed Γ (Term.var x) E C0) :
  Typed Γ (Term.var x) E {} :=
  Typed.precise_cv' rfl h

theorem Typed.ssub
  (h : Γ[C] ⊢ t : E)
  (hsub : Γ ⊢ E <:e E') :
  Γ[C] ⊢ t : E' := by
  apply Typed.sub
  exact h
  apply Subcapt.refl
  exact hsub

end Capless
