import Capless.Anchoring
namespace Capless

theorem EType.AnchorCapture.trename
  (h : EType.AnchorCapture E C E') :
  EType.AnchorCapture (E.trename f) C (E'.trename f) := by
  cases h <;> (constructor; try easy)

theorem EType.AnchorType.trename
  (h : EType.AnchorType E C E') :
  EType.AnchorType (E.trename f) C (E'.trename f) := by
  cases h <;> constructor

theorem SType.AnchorUniversal.trename
  (h : SType.AnchorUniversal S C S') :
  SType.AnchorUniversal (S.trename f) C (S'.trename f) := by
  cases h <;> constructor
  case tarrow => apply EType.AnchorType.trename; easy
  case carrow => apply EType.AnchorCapture.trename; easy

theorem SType.Anchor.trename
  (h : SType.Anchor S C T) :
  SType.Anchor (S.trename f) C (T.trename f) := by
  cases h
  case capt =>
    constructor
    apply SType.AnchorUniversal.trename
    easy

end Capless
