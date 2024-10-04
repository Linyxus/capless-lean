import Capless.Inversion.Basic
import Capless.Inversion.Context
namespace Capless

theorem SType.dealias_inj {S : SType n m k}
  (hd1 : SType.Dealias Γ S S1)
  (hd2 : SType.Dealias Γ S S2) :
  (S1.IsVar) ∨ (S2.IsVar) ∨ (S1 = S2) := by
  induction hd1 generalizing S2
  case refl =>
    cases hd2
    case refl => aesop
    case step => constructor; constructor
  case step hb1 _ ih =>
    cases hd2
    case refl => apply Or.inr; constructor; constructor
    case step hb2 hd2 =>
      have h := Context.tbound_inj hb1 hb2
      cases h
      aesop

end Capless
