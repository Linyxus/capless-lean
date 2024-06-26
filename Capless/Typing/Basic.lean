import Capless.Typing
import Capless.Subcapturing
import Capless.Subcapturing.Basic
import Capless.Subtyping.Basic
namespace Capless

-- inductive EType.TryOpen : Fin n -> EType n m k -> CType n m k -> Prop where
-- | type :
--   TryOpen x (EType.type T) T
-- | exist :
--   TryOpen x (EType.exist T) (T.)

theorem Typing.inv_subcapt'
  (he1 : t0 = Term.var x) (he2 : E0 = EType.type (CType.capt C S))
  (h : Typed Γ t0 E0) :
  Subcapt Γ {x} C := by
  induction h <;> try (solve | cases he1 | cases he2)
  case var =>
    cases he1; subst he2
    apply Subcapt.var
    trivial
  case exists_elim =>
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
  (h : Typed Γ (Term.var x) (EType.type (CType.capt C S))) :
  Subcapt Γ {x} C :=
  Typing.inv_subcapt' rfl rfl h

theorem Typing.inv_var_exists'
  (he1 : t0 = Term.var x) (he2 : E0 = EType.ex (CType.capt C.cweaken S))
  (h : Typed Γ t0 E0) :
  Subcapt Γ {x} C := by
  induction h <;> try (solve | cases he1 | cases he2)
  case var =>
    cases he1; subst he2; apply Subcapt.evar; trivial
  case sub hs ih =>
    subst he1 he2
    sorry

theorem Typing.inv_var_exists
  (h : Typed Γ (Term.var x) (EType.ex (CType.capt C.cweaken S))) :
  Subcapt Γ {x} C := sorry

end Capless
