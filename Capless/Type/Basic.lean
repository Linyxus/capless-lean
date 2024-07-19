import Capless.Type
namespace Capless

theorem SType.tvar_tweaken_succ :
  (SType.tvar X : SType n m k).tweaken = SType.tvar X.succ := by
  simp [SType.tweaken, SType.trename, FinFun.weaken]

end Capless
