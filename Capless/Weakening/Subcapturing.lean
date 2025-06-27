import Capless.Weakening.Basic
import Capless.Renaming.Term.Subtyping
import Capless.Renaming.Type.Subtyping
import Capless.Renaming.Capture.Subtyping

/-!
# Subcapturing Weakening

This file establishes weakening properties for subcapturing judgments in the Capless type system.
Subcapturing relations express when one capture set is contained within another, and these
relations must be preserved when extending contexts.

The file provides weakening theorems for:
- `Subcapt.weaken`: Regular variable weakening for subcapturing judgments
- `Subcapt.tweaken`: Type variable weakening for subcapturing judgments
- `Subcapt.cweaken`: Capture variable weakening for subcapturing judgments

These results ensure that subcapturing relationships remain valid when new variables are
introduced into the typing context.
-/

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
