import Capless.Subtyping
namespace Capless

theorem ESubtyp.sub_type_inv'
  (he : E2 = EType.type T2)
  (h : ESubtyp Γ E1 E2) :
  ∃ T1, E1 = EType.type T1 ∧ CSubtyp Γ T1 T2 := by
  cases h <;> try (solve | cases he)
  case type T1 T2 hs =>
    cases he
    exists T1

theorem ESubtyp.sub_type_inv
  (h : ESubtyp Γ E1 (EType.type T2)) :
  ∃ T1, E1 = EType.type T1 ∧ CSubtyp Γ T1 T2 := by
  apply ESubtyp.sub_type_inv' rfl h

-- theorem SSubtyp.sub_forall_inv
--   (h : SSubtyp Γ S1 (SType.forall T E)) :
--   ∃

end Capless
