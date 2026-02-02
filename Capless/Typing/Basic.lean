import Capless.Typing
import Capless.Subcapturing
import Capless.Subcapturing.Basic
import Capless.Subtyping.Basic

/-!
# Basic Properties of Typing

This file contains basic properties of the typing relation.
-/

namespace Capless

theorem Typing.inv_subcapt'
  (he1 : t0 = Term.var x) (he2 : E0 = EType.type (CType.capt C S))
  (h : Typed Γ t0 E0 C0) :
  Subcapt Γ {x=x|.top} C := by
  induction h <;> try (solve | cases he1 | cases he2)
  case var =>
    cases he1; cases he2
    apply Subcapt.rfl
  case label =>
    cases he1; cases he2
    apply Subcapt.rfl
  case sub hsub ih =>
    subst he1 he2
    have h := ESubtyp.type_inv_subcapt hsub
    let ⟨C0, S0, he, hs⟩ := h
    subst he
    have ih := ih rfl rfl
    apply Subcapt.trans; trivial; trivial

theorem Typing.inv_subcapt
  (h : Typed Γ (Term.var x) (EType.type (CType.capt C S)) C0) :
  Subcapt Γ {x=x|.top} C :=
  Typing.inv_subcapt' rfl rfl h

theorem Typed.bound_typing
  (hb : Context.Bound Γ x T) :
  Typed Γ (Term.var x) (EType.type T) {x=x|.top} := by
  cases T
  apply Typed.sub
  apply Typed.var hb
  apply Subcapt.rfl
  constructor
  constructor
  have h := Subcapt.var hb (L:=.top); rw [CaptureSet.proj_top] at h; assumption
  apply SSubtyp.refl

theorem Typed.precise_capture'
  (he1 : t0 = Term.var x)
  (he2 : E0 = EType.type (CType.capt C S))
  (h : Typed Γ t0 E0 C0) :
  Typed Γ (Term.var x) (EType.type (CType.capt {x=x|.top} S)) {x=x|.top} := by
  induction h <;> try (solve | cases he1 | cases he2)
  case var => cases he1; cases he2; apply Typed.var; trivial
  case label => cases he1; cases he2; apply Typed.label; trivial
  case sub hsub ih =>
    subst_vars
    cases hsub
    rename_i hsub
    cases hsub
    rename_i hsc hss
    have ih := ih rfl rfl
    apply Typed.sub
    { exact ih }
    { apply Subcapt.rfl }
    { constructor
      constructor
      apply Subcapt.rfl
      trivial }

theorem Typed.precise_capture
  (h : Typed Γ (Term.var x) (EType.type (CType.capt C S)) C0) :
  Typed Γ (Term.var x) (EType.type (CType.capt {x=x|.top} S)) {x=x|.top} :=
  Typed.precise_capture' rfl rfl h

theorem Typed.precise_cv'
  (he : t0 = Term.var x)
  (h : Typed Γ t0 E C0) :
  Typed Γ (Term.var x) E {x=x|.top} := by
  induction h <;> try (solve | cases he)
  case var => cases he; apply Typed.var; trivial
  case label => cases he; apply Typed.label; trivial
  case sub ih =>
    apply Typed.sub
    { apply! ih }
    { apply Subcapt.rfl }
    { trivial }

theorem Typed.precise_cv
  (h : Typed Γ (Term.var x) E C0) :
  Typed Γ (Term.var x) E {x=x|.top} :=
  Typed.precise_cv' rfl h

end Capless
