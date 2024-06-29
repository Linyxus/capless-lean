import Capless.Subtyping
import Capless.Subcapturing
import Capless.Subcapturing.Basic
namespace Capless

theorem ESubtyp.type_inv_subcapt'
  (heq : E1 = EType.type (CType.capt C S))
  (h : ESubtyp Γ E E1) :
  ∃ C0 S0, E = EType.type (CType.capt C0 S0) ∧ Subcapt Γ C0 C := by
  cases h
  case type T1 _ _ =>
    cases T1
    cases heq
    constructor; constructor; constructor
    rfl
    rename_i h; cases h; trivial
  case exist => cases heq

theorem ESubtyp.type_inv_subcapt
  (h : ESubtyp Γ E (EType.type (CType.capt C S))) :
  ∃ C0 S0, E = EType.type (CType.capt C0 S0) ∧ Subcapt Γ C0 C :=
  ESubtyp.type_inv_subcapt' rfl h

theorem ESubtyp.ex_inv_subcapt
  (h : ESubtyp Γ E (EType.ex (CType.capt C S))) :
  ∃ C0 S0, E = EType.ex (CType.capt C0 S0) ∧ Subcapt (Γ.cvar CBinding.bound) C0 C := by
  cases h
  case exist hs =>
    cases hs
    constructor; constructor; constructor
    rfl
    trivial

end Capless
