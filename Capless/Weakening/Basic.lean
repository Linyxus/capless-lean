import Capless.Renaming.Basic
namespace Capless

def VarMap.weaken {Γ : Context n m k} :
  VarMap Γ FinFun.weaken (Γ.var T) := by
  constructor <;> (intros; constructor; trivial)

def CVarMap.weaken {Γ : Context n m k} :
  CVarMap Γ FinFun.weaken (Γ.cvar b) := by
  constructor <;> (intros; constructor; trivial)

def TVarMap.weaken {Γ : Context n m k} :
  TVarMap Γ FinFun.weaken (Γ.tvar b) := by
  constructor <;> (intros; constructor; trivial)

end Capless
