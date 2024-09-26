import Capless.Weakening.Basic
import Capless.Renaming.Term.Subtyping
import Capless.Renaming.Type.Subtyping
import Capless.Renaming.Capture.Subtyping
namespace Capless

theorem SSubtyp.weaken
  (h : SSubtyp Γ S1 S2) :
  ∀ b, SSubtyp (Γ.var b) S1.weaken S2.weaken := by
  intro b
  simp [SType.weaken]
  apply SSubtyp.rename
  { apply h }
  { apply VarMap.weaken }

theorem CSubtyp.weaken
  (h : CSubtyp Γ E1 E2) :
  CSubtyp (Γ.var T) E1.weaken E2.weaken := by
  simp [CType.weaken]
  apply CSubtyp.rename
  { apply h }
  { apply VarMap.weaken }

theorem ESubtyp.weaken
  (h : ESubtyp Γ E1 E2) :
  ESubtyp (Γ.var T) E1.weaken E2.weaken := by
  simp [EType.weaken]
  apply ESubtyp.rename
  { apply h }
  { apply VarMap.weaken }

theorem SSubtyp.tweaken
  (h : SSubtyp Γ S1 S2) :
  SSubtyp (Γ.tvar b) S1.tweaken S2.tweaken := by
  simp [SType.tweaken]
  apply? SSubtyp.trename
  apply TVarMap.weaken

theorem ESubtyp.tweaken
  (h : ESubtyp Γ E1 E2) :
  ESubtyp (Γ.tvar b) E1.tweaken E2.tweaken := by
  simp [EType.tweaken]
  apply? ESubtyp.trename
  apply TVarMap.weaken

theorem CSubtyp.tweaken
  (h : CSubtyp Γ E1 E2) :
  CSubtyp (Γ.tvar b) E1.tweaken E2.tweaken := by
  simp [CType.tweaken]
  apply? CSubtyp.trename
  apply TVarMap.weaken

theorem ESubtyp.cweaken
  (h : ESubtyp Γ E1 E2) :
  ESubtyp (Γ.cvar b) E1.cweaken E2.cweaken := by
  apply? ESubtyp.crename
  apply CVarMap.weaken

theorem SSubtyp.cweaken
  (h : SSubtyp Γ S1 S2) :
  ∀ b, SSubtyp (Γ.cvar b) S1.cweaken S2.cweaken := by
  intro b
  simp [SType.cweaken]
  apply? SSubtyp.crename
  apply CVarMap.weaken

theorem CSubtyp.cweaken
  (h : CSubtyp Γ E1 E2) :
  CSubtyp (Γ.cvar b) E1.cweaken E2.cweaken := by
  simp [CType.cweaken]
  apply? CSubtyp.crename
  apply CVarMap.weaken

end Capless
