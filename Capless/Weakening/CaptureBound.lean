import Capless.CaptureBound
import Capless.Weakening.Basic
import Capless.Renaming.Term.CaptureBound
import Capless.Renaming.Type.CaptureBound
import Capless.Renaming.Capture.CaptureBound

namespace Capless

def CaptureKind.weaken
  (h : CaptureKind Γ C K) :
   CaptureKind (Γ,x: T) C.weaken K := by
  apply h.rename VarMap.weaken

def CaptureKind.tweaken
  (h : CaptureKind Γ C K) :
  CaptureKind (Γ.tvar b) C K := by
  apply h.trename TVarMap.weaken

def CaptureKind.cweaken
  (h : CaptureKind Γ C K) :
  CaptureKind (Γ.cvar b) C.cweaken K := by
  apply h.crename CVarMap.weaken
