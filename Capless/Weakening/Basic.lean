import Capless.Renaming.Basic
namespace Capless

def VarMap.weaken {Γ : Context n m k} :
  VarMap Γ FinFun.weaken (Γ.var T) := by
  constructor <;> (intros; constructor; trivial)

def VarMap.weaken_ext {Γ : Context n m k} :
  VarMap
    (Γ.var T)
    FinFun.weaken.ext
    ((Γ.var P).var T.weaken) := by
  apply VarMap.ext
  apply VarMap.weaken

def VarMap.weaken_cext_ext {Γ : Context n m k} :
  VarMap
    ((Γ.cvar CBinding.bound).var T)
    FinFun.weaken.ext
    (((Γ.var P).cvar CBinding.bound).var T.weaken) := by
  apply VarMap.ext
  apply VarMap.cext
  apply VarMap.weaken

def CVarMap.weaken {Γ : Context n m k} :
  CVarMap Γ FinFun.weaken (Γ.cvar b) := by
  constructor <;> (intros; constructor; trivial)

def TVarMap.weaken {Γ : Context n m k} :
  TVarMap Γ FinFun.weaken (Γ.tvar b) := by
  constructor <;> (intros; constructor; trivial)

def TVarMap.weaken_ext {Γ : Context n m k} :
  TVarMap
    (Γ.var T)
    FinFun.weaken
    ((Γ.tvar b).var T.tweaken) := by
  apply TVarMap.ext
  apply TVarMap.weaken

end Capless
