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

theorem CSubtyp.refl :
  CSubtyp Γ T T := by
  cases T; apply capt
  { apply Subcapt.refl }
  { apply SSubtyp.refl }

theorem ESubtyp.refl :
  ESubtyp Γ E E := by
  cases E
  case ex =>
    apply exist
    apply CSubtyp.refl
  case type =>
    apply type
    apply CSubtyp.refl

theorem CSubtyp.trans
  (h1 : CSubtyp Γ T1 T2)
  (h2 : CSubtyp Γ T2 T3) :
  CSubtyp Γ T1 T3 := by
  cases h1; cases h2
  rename_i _ _ hc1 hs1 _ _ hc2 hs2
  constructor
  apply Subcapt.trans <;> trivial
  apply SSubtyp.trans <;> trivial

theorem ESubtyp.trans
  (h1 : ESubtyp Γ E1 E2)
  (h2 : ESubtyp Γ E2 E3) :
  ESubtyp Γ E1 E3 := by
  cases h1 <;> cases h2
  { apply exist
    apply CSubtyp.trans
    { trivial }
    { trivial } }
  { apply type
    apply CSubtyp.trans
    { trivial }
    { trivial } }

end Capless
