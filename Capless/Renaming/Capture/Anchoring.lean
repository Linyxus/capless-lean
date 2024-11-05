import Capless.Anchoring
namespace Capless

theorem CaptureSet.AnchorCapture.crename
  (h : CaptureSet.AnchorCapture C D C') :
  CaptureSet.AnchorCapture (C.crename (FinFun.ext f)) (D.crename f) (C'.crename f.ext) := by
  cases h
  case anchor C0 =>
    simp [FinFun.ext]
    simp [<- CaptureSet.cweaken_crename]
    constructor
  case anchor_devoid =>
    simp [<- CaptureSet.cweaken_crename]
    constructor

theorem EType.AnchorCapture.crename
  (h : EType.AnchorCapture E C E') :
  EType.AnchorCapture (E.crename (FinFun.ext f)) (C.crename f) (E'.crename f.ext) := by
  cases h <;> constructor
  apply CaptureSet.AnchorCapture.crename; easy

theorem EType.AnchorType.crename
  (h : EType.AnchorType E C E') :
  EType.AnchorType (E.crename f) (C.crename f) (E'.crename f) := by
  cases h <;> constructor

theorem SType.AnchorUniversal.crename
  (h : SType.AnchorUniversal S C S') :
  SType.AnchorUniversal (S.crename f) (C.crename f) (S'.crename f) := by
  cases h <;> constructor
  case tarrow =>
    apply EType.AnchorType.crename; easy
  case carrow =>
    apply EType.AnchorCapture.crename; easy

theorem SType.Anchor.crename
  (h : SType.Anchor S C T) :
  SType.Anchor (S.crename f) (C.crename f) (T.crename f) := by
  cases h
  case capt =>
    constructor
    apply SType.AnchorUniversal.crename
    easy

end Capless
