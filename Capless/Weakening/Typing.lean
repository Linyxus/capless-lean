import Capless.Renaming.Term.Typing
import Capless.Renaming.Type.Typing
import Capless.Renaming.Capture.Typing
namespace Capless

theorem Typed.weaken
  (h : Typed Γ t E) :
  Typed (Γ.var T) t.weaken E.weaken := by
  simp [Term.weaken, EType.weaken]
  apply Typed.rename h
  apply VarMap.weaken

def Typed.tweaken
  (h : Typed Γ t E) :
  Typed (Γ.tvar b) t.tweaken E.tweaken := by
  simp [Term.tweaken, EType.tweaken]
  apply h.trename
  apply TVarMap.weaken

def Typed.cweaken
  (h : Typed Γ t E) :
  Typed (Γ.cvar b) t.cweaken E.cweaken := by
  simp [Term.cweaken, EType.cweaken]
  apply h.crename
  apply CVarMap.weaken


end Capless
