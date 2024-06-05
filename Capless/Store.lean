import Capless.Term
import Capless.Type
import Capless.CaptureSet
import Capless.Context
import Capless.Typing
namespace Capless

inductive Store : Nat -> Nat -> Nat -> Type where
| empty : Store 0 0 0
| val :
  Store n m k ->
  (t : Term n m k) ->
  t.IsValue ->
  Store (n+1) m k
| tval :
  Store n m k ->
  SType n m k ->
  Store n (m+1) k
| cval :
  Store n m k ->
  CaptureSet n k ->
  Store n m (k+1)

inductive TypedStore : Store n m k -> Context n m k -> Prop where
| empty : TypedStore Store.empty Context.empty
| val :
  TypedStore σ Γ ->
  Typed Γ t E ->
  (hv : t.IsValue) ->
  TypedStore (Store.val σ t hv) (Γ.var E)
| tval :
  TypedStore σ Γ ->
  TypedStore (Store.tval σ S) (Γ.tvar (TBinding.inst S))
| cval :
  TypedStore σ Γ ->
  TypedStore (Store.cval σ C) (Γ.cvar (CBinding.inst C))

inductive Store.Bound : Store n m k -> (Fin n) -> Term n m k -> Prop where
| here :
  Store.Bound (Store.val σ t hv) 0 t.weaken
| there_val :
  Store.Bound σ x t ->
  Store.Bound (Store.val σ t' hv) (Fin.succ x) t.weaken
| there_tval :
  Store.Bound σ x t ->
  Store.Bound (Store.tval σ S) x t.tweaken
| there_cval :
  Store.Bound σ x t ->
  Store.Bound (Store.cval σ C) x t.cweaken

inductive Store.TBound : Store n m k -> (Fin m) -> SType n m k -> Prop where
| here :
  Store.TBound (Store.tval σ S) 0 S.tweaken
| there_val :
  Store.TBound σ x S ->
  Store.TBound (Store.val σ t hv) x S.weaken
| there_tval :
  Store.TBound σ x S ->
  Store.TBound (Store.tval σ S') (Fin.succ x) S.tweaken
| there_cval :
  Store.TBound σ x S ->
  Store.TBound (Store.cval σ C) x S.cweaken

inductive Store.CBound : Store n m k -> (Fin k) -> CaptureSet n k -> Prop where
| here :
  Store.CBound (Store.cval σ C) 0 C.cweaken
| there_val :
  Store.CBound σ x C ->
  Store.CBound (Store.val σ t hv) x C.weaken
| there_tval :
  Store.CBound σ x C ->
  Store.CBound (Store.tval σ S) x C
| there_cval :
  Store.CBound σ x C ->
  Store.CBound (Store.cval σ C') (Fin.succ x) C.cweaken


end Capless
