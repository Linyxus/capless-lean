import Capless.Store
namespace Capless

theorem TypedCont.narrow
  (h : TypedCont Γ E1 cont E)
  (hsub : ESubtyp Γ E2 E1) :
  TypedCont Γ E2 cont E := by
  cases h
  case none => sorry
  case cons => sorry
  case conse => sorry

end Capless
