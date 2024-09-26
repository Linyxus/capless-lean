import Capless.Weakening.Basic
import Capless.Renaming.Term.Subtyping
import Capless.Renaming.Type.Subtyping
import Capless.Renaming.Capture.Subtyping
namespace Capless

def Subcapt.weaken
  (h : Γ ⊢ C1 <:c C2) :
  (Γ,x: T) ⊢ C1.weaken <:c C2.weaken := by
  apply h.rename VarMap.weaken

def Subcapt.tweaken
  (h : Γ ⊢ C1 <:c C2) :
  (Γ.tvar b) ⊢ C1 <:c C2 := by
  apply h.trename TVarMap.weaken

def Subcapt.cweaken
  (h : Γ ⊢ C1 <:c C2) :
  (Γ.cvar b) ⊢ C1.cweaken <:c C2.cweaken := by
  apply h.crename CVarMap.weaken

end Capless
