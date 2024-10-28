import Cappy.Translation.Encoding.Type
import Cappy.Translation.TContext
namespace Cappy

inductive Context.Interp : Context n m -> TContext n m k -> Prop where
| empty :
  Context.Interp empty TContext.empty
| var {Γ : Context n m} {Δ : TContext n m k} :
  Context.Interp Γ Δ ->
  CType.Interp (Δ.map.cweaken) Γ T {c=0} T' ->
  Context.Interp (Γ.var T) (Δ.var T')
| tvar {Γ : Context n m} {Δ : TContext n m k} :
  Context.Interp Γ Δ ->
  CType.Interp (Δ.map.cweaken) Γ (S^{}) {c=0} (S'^{}) ->
  Context.Interp (Γ.tvar S) (Δ.tvar S')

end Cappy
