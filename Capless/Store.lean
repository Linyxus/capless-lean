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

inductive Cont : Nat -> Nat -> Nat -> Type where
| none : Cont n m k
| cons :
  (t : Term (n+1) m k) ->
  (cont : Cont n m k) ->
  Cont n m k
| conse :
  (t : Term (n+1) m (k+1)) ->
  (cont : Cont n m k) ->
  Cont n m k

structure State (n : Nat) (m : Nat) (k : Nat) where
  σ : Store n m k
  cont : Cont n m k
  t : Term n m k

inductive TypedStore : Store n m k -> Context n m k -> Prop where
| empty : TypedStore Store.empty Context.empty
| val :
  TypedStore σ Γ ->
  Typed Γ t (EType.type E) ->
  (hv : t.IsValue) ->
  TypedStore (Store.val σ t hv) (Γ.var E)
| tval :
  TypedStore σ Γ ->
  TypedStore (Store.tval σ S) (Γ.tvar (TBinding.inst S))
| cval :
  TypedStore σ Γ ->
  TypedStore (Store.cval σ C) (Γ.cvar (CBinding.inst C))

inductive TypedCont : Context n m k -> EType n m k -> Cont n m k -> EType n m k -> Prop where
| none :
  TypedCont Γ E Cont.none E
| cons :
  Typed (Γ.var T) t (EType.weaken E) ->
  TypedCont Γ E cont E' ->
  TypedCont Γ (EType.type T) (Cont.cons t cont) E'
| conse :
  Typed ((Γ.cvar CBinding.bound).var T) t (EType.weaken (EType.cweaken E)) ->
  TypedCont Γ E cont E' ->
  TypedCont Γ (EType.ex T) (Cont.conse t cont) E'

inductive TypedState : State n m k -> EType n m k -> Prop where
| mk :
  TypedStore σ Γ ->
  Typed Γ t E ->
  TypedCont Γ E cont E' ->
  TypedState (State.mk σ cont t) E'

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

def Cont.weaken : Cont n m k -> Cont (n+1) m k
| Cont.none => Cont.none
| Cont.cons t cont => Cont.cons t.weaken1 cont.weaken
| Cont.conse t cont => Cont.conse t.weaken1 cont.weaken

def Cont.tweaken : Cont n m k -> Cont n (m+1) k
| Cont.none => Cont.none
| Cont.cons t cont => Cont.cons t.tweaken cont.tweaken
| Cont.conse t cont => Cont.conse t.tweaken cont.tweaken

def Cont.cweaken : Cont n m k -> Cont n m (k+1)
| Cont.none => Cont.none
| Cont.cons t cont => Cont.cons t.cweaken cont.cweaken
| Cont.conse t cont => Cont.conse t.cweaken1 cont.cweaken

inductive Context.IsTight : Context n m k -> Prop where
| empty : Context.IsTight Context.empty
| var :
  Context.IsTight Γ ->
  Context.IsTight (Γ.var T)
| tvar :
  Context.IsTight Γ ->
  Context.IsTight (Γ.tvar (TBinding.inst S))
| cvar :
  Context.IsTight Γ ->
  Context.IsTight (Γ.cvar (CBinding.inst C))

theorem TypedStore.is_tight
  (h : TypedStore σ Γ) :
  Γ.IsTight := by
  induction h
  case empty => constructor
  case val ih => constructor; trivial
  case tval ih => constructor; trivial
  case cval ih => constructor; trivial

end Capless
