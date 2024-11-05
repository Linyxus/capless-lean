import Capless.Anchoring
namespace Capless

theorem CaptureSet.AnchorCapture.rename
  (h : CaptureSet.AnchorCapture C1 D C2) :
  CaptureSet.AnchorCapture (C1.rename f) (D.rename f) (C2.rename f) := by
  cases h
  case anchor =>
    simp
    simp [CaptureSet.cweaken_rename_comm]
    constructor
  case anchor_devoid =>
    simp [CaptureSet.cweaken_rename_comm]
    constructor

theorem EType.AnchorCapture.rename
  (h : EType.AnchorCapture T1 C1 T2) :
  EType.AnchorCapture (T1.rename f) (C1.rename f) (T2.rename f) := by
  cases h
  case ex => constructor
  case type =>
    constructor
    apply CaptureSet.AnchorCapture.rename; easy

theorem EType.AnchorType.rename
  (h : EType.AnchorType T1 C1 T2) :
  EType.AnchorType (T1.rename f) (C1.rename f) (T2.rename f) := by
  cases h <;> constructor

theorem SType.AnchorUniversal.rename
  (h : SType.AnchorUniversal S1 C1 S2) :
  SType.AnchorUniversal (S1.rename f) (C1.rename f) (S2.rename f) := by
  cases h <;> constructor
  case tarrow => apply EType.AnchorType.rename; easy
  case carrow => apply EType.AnchorCapture.rename; easy

theorem SType.Anchor.rename
  (h : SType.Anchor S1 C1 S2) :
  SType.Anchor (S1.rename f) (C1.rename f) (S2.rename f) := by
  cases h
  constructor
  apply SType.AnchorUniversal.rename; easy

end Capless
