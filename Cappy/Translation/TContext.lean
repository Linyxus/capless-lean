import Capless.Context
import Capless.Basic
import Cappy.Translation.TMap
namespace Cappy

structure TContext (n m k : Nat) where
  ctx : Capless.Context n m k
  map : TMap n m k

def TContext.empty : TContext 0 0 0 :=
  ⟨Capless.Context.empty, TMap.empty⟩

def TContext.var (Γ : TContext n m k) : TContext (n+1) m (k+1) := sorry

end Cappy
