import Capless.Context
import Capless.Basic
import Cappy.Translation.TMap
namespace Cappy

structure TContext (n m k : Nat) where
  ctx : Capless.Context n m k
  map : TMap n m k

def TContext.empty : TContext 0 0 0 :=
  ⟨Capless.Context.empty, TMap.empty⟩

def TContext.var
  (Γ : TContext n m k)
  (T : Capless.CType n m (k+1)) :
  TContext (n+1) m (k+1) :=
  ⟨((Γ.ctx,c:CapSet),x:T), Γ.map.ext⟩

def TContext.tvar
  (Γ : TContext n m k)
  (S : Capless.SType n m (k+1)) :
  TContext n (m+1) (k+1) :=
  ⟨((Γ.ctx,c:CapSet),X<:S), Γ.map.text⟩

end Cappy
