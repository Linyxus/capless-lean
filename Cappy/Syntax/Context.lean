import Cappy.Syntax.Type
namespace Cappy

inductive Context : Nat -> Nat -> Type where
| empty : Context 0 0
| var : Context n m -> CType n m -> Context (n+1) m
| tvar : Context n m -> SType n m -> Context n (m+1)

inductive Context.Bound : Context n m -> Fin n -> CType n m -> Prop where
| here :
  Context.Bound (Context.var Γ T) 0 T.weaken
| there_var :
  Context.Bound Γ x T ->
  Context.Bound (Context.var Γ T') x.succ T.weaken
| there_tvar :
  Context.Bound Γ x T ->
  Context.Bound (Context.tvar Γ S) x T.tweaken

inductive Context.TBound : Context n m -> Fin m -> SType n m -> Prop where
| here :
  Context.TBound (Context.tvar Γ S) 0 S.tweaken
| there_var :
  Context.TBound Γ x S ->
  Context.TBound (Context.var Γ T) x S.weaken
| there_tvar :
  Context.TBound Γ x S ->
  Context.TBound (Context.tvar Γ S') x.succ S.tweaken

end Cappy
