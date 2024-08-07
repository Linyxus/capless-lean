import Capless.Weakening.Basic
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

theorem Typed.weaken_ext {Γ : Context n m k}
  (h : Typed (Γ.var T) t E) :
  Typed ((Γ.var P).var T.weaken) t.weaken1 E.weaken1 := by
  simp [Term.weaken1, EType.weaken1]
  apply h.rename VarMap.weaken_ext

theorem Typed.weaken_cext_ext {Γ : Context n m k}
  (h : Typed ((Γ.cvar CBinding.bound).var T) t E) :
  Typed (((Γ.var P).cvar CBinding.bound).var T.weaken) t.weaken1 E.weaken1 := by
  simp [Term.weaken1, EType.weaken1]
  apply h.rename VarMap.weaken_cext_ext

def Typed.tweaken
  (h : Typed Γ t E) :
  Typed (Γ.tvar b) t.tweaken E.tweaken := by
  simp [Term.tweaken, EType.tweaken]
  apply h.trename
  apply TVarMap.weaken

theorem Typed.tweaken_ext {Γ : Context n m k}
  (h : Typed (Γ.var T) t E) :
  Typed ((Γ.tvar b).var T.tweaken) t.tweaken E.tweaken := by
  simp [Term.tweaken, EType.tweaken]
  apply h.trename TVarMap.weaken_ext

theorem Typed.tweaken_cext_ext {Γ : Context n m k}
  (h : Typed ((Γ.cvar CBinding.bound).var T) t E) :
  Typed (((Γ.tvar b).cvar CBinding.bound).var T.tweaken) t.tweaken E.tweaken := by
  simp [Term.tweaken, EType.tweaken]
  apply h.trename TVarMap.weaken_cext_ext

def Typed.cweaken
  (h : Typed Γ t E) :
  Typed (Γ.cvar b) t.cweaken E.cweaken := by
  simp [Term.cweaken, EType.cweaken]
  apply h.crename
  apply CVarMap.weaken

def Typed.cweaken_ext {Γ : Context n m k}
  (h : Typed (Γ.var T) t E) :
  Typed ((Γ.cvar b).var T.cweaken) t.cweaken E.cweaken := by
  simp [Term.cweaken, EType.cweaken]
  apply h.crename CVarMap.weaken_ext

def Typed.cweaken_cext_ext {Γ : Context n m k}
  (h : Typed ((Γ.cvar CBinding.bound).var T) t E) :
  Typed (((Γ.cvar b).cvar CBinding.bound).var T.cweaken1) t.cweaken1 E.cweaken1 := by
  simp [Term.cweaken, EType.cweaken1]
  apply h.crename CVarMap.weaken_cext_ext

end Capless
