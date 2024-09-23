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
| label :
  Store n m k ->
  SType n m k ->
  Store (n+1) m k

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
| scope :
  (l : Fin n) ->
  Cont n m k ->
  Cont n m k

structure State (n : Nat) (m : Nat) (k : Nat) where
  σ : Store n m k
  cont : Cont n m k
  t : Term n m k

inductive TypedStore : Store n m k -> Context n m k -> Prop where
| empty : TypedStore Store.empty Context.empty
| val :
  TypedStore σ Γ ->
  Typed Γ t (EType.type E) Ct ->
  (hv : t.IsValue) ->
  TypedStore (Store.val σ t hv) (Γ.var E)
| tval :
  TypedStore σ Γ ->
  TypedStore (Store.tval σ S) (Γ.tvar (TBinding.inst S))
| cval :
  TypedStore σ Γ ->
  TypedStore (Store.cval σ C) (Γ.cvar (CBinding.inst C))
| label :
  TypedStore σ Γ ->
  TypedStore (Store.label σ S) (Γ.label S)

inductive Cont.HasLabel : Cont n m k -> Fin n -> Cont n m k -> Prop where
| here :
  Cont.HasLabel (Cont.scope l tail) l tail
| there_val :
  Cont.HasLabel cont l tail ->
  Cont.HasLabel (Cont.cons t cont) l tail
| there_tval :
  Cont.HasLabel cont l tail ->
  Cont.HasLabel (Cont.conse t cont) l tail
| there_cval :
  Cont.HasLabel cont l tail ->
  Cont.HasLabel (Cont.scope l' cont) l tail
| there_label :
  Cont.HasLabel cont l tail ->
  Cont.HasLabel (Cont.scope l' cont) l tail

inductive WellScoped : Context n m k -> Cont n m k -> CaptureSet n k -> Prop where
| empty :
  WellScoped Γ cont {}
| union :
  WellScoped Γ cont C1 ->
  WellScoped Γ cont C2 ->
  WellScoped Γ cont (C1 ∪ C2)
| singleton :
  Context.Bound Γ x (S^C) ->
  WellScoped Γ cont C ->
  WellScoped Γ cont {x=x}
| csingleton :
  Context.CBound Γ c (CBinding.inst C) ->
  WellScoped Γ cont C ->
  WellScoped Γ cont {c=c}
| label :
  Context.LBound Γ x S ->
  Cont.HasLabel cont x tail ->
  WellScoped Γ cont {x=x}

inductive TypedCont : Context n m k -> EType n m k -> Cont n m k -> EType n m k -> CaptureSet n k -> Prop where
| none :
  ESubtyp Γ E E' ->
  TypedCont Γ E Cont.none E' {}
| cons {Ct : CaptureSet n k} :
  Typed (Γ,x: T) t (EType.weaken E) Ct.weaken ->
  WellScoped Γ cont Ct ->
  TypedCont Γ E cont E' C ->
  TypedCont Γ (EType.type T) (Cont.cons t cont) E' (C ∪ Ct)
| conse {Ct : CaptureSet n k} :
  Typed ((Γ.cvar CBinding.bound).var T) t (EType.weaken (EType.cweaken E)) Ct.cweaken.weaken ->
  WellScoped Γ cont Ct ->
  TypedCont Γ E cont E' C ->
  TypedCont Γ (EType.ex T) (Cont.conse t cont) E' (C ∪ Ct)
| scope :
  Context.LBound Γ x S ->
  TypedCont Γ (S^{}) cont E' C ->
  TypedCont Γ (S^{}) (Cont.scope x cont) E' C

inductive TypedState : State n m k -> Context n m k -> EType n m k -> Prop where
| mk :
  TypedStore σ Γ ->
  Typed Γ t E Ct ->
  WellScoped Γ cont Ct ->
  TypedCont Γ E cont E' C ->
  TypedState (State.mk σ cont t) Γ E'

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
| there_label :
  Store.Bound σ x t ->
  Store.Bound (Store.label σ S) (Fin.succ x) t.weaken

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
| there_label :
  Store.TBound σ x S ->
  Store.TBound (Store.label σ S') x S.weaken

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
| there_label :
  Store.CBound σ x C ->
  Store.CBound (Store.label σ S) x C.weaken

inductive Store.LBound : Store n m k -> (Fin n) -> SType n m k -> Prop where
| here :
  Store.LBound (Store.label σ S) 0 S.weaken
| there_val :
  Store.LBound σ x S ->
  Store.LBound (Store.val σ t hv) x.succ S.weaken
| there_tval :
  Store.LBound σ x S ->
  Store.LBound (Store.tval σ S') x S.tweaken
| there_cval :
  Store.LBound σ x S ->
  Store.LBound (Store.cval σ C) x S.cweaken
| there_label :
  Store.LBound σ x S ->
  Store.LBound (Store.label σ S') x.succ S.weaken

def Cont.weaken : Cont n m k -> Cont (n+1) m k
| Cont.none => Cont.none
| Cont.cons t cont => Cont.cons t.weaken1 cont.weaken
| Cont.conse t cont => Cont.conse t.weaken1 cont.weaken
| Cont.scope x cont => Cont.scope x.succ cont.weaken

def Cont.tweaken : Cont n m k -> Cont n (m+1) k
| Cont.none => Cont.none
| Cont.cons t cont => Cont.cons t.tweaken cont.tweaken
| Cont.conse t cont => Cont.conse t.tweaken cont.tweaken
| Cont.scope x cont => Cont.scope x cont.tweaken

def Cont.cweaken : Cont n m k -> Cont n m (k+1)
| Cont.none => Cont.none
| Cont.cons t cont => Cont.cons t.cweaken cont.cweaken
| Cont.conse t cont => Cont.conse t.cweaken1 cont.cweaken
| Cont.scope x cont => Cont.scope x cont.cweaken

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
| label :
  Context.IsTight Γ ->
  Context.IsTight (Γ.label S)

theorem TypedStore.is_tight
  (h : TypedStore σ Γ) :
  Γ.IsTight := by
  induction h
  case empty => constructor
  case val ih => constructor; trivial
  case tval ih => constructor; trivial
  case cval ih => constructor; trivial
  case label ih => constructor; trivial

end Capless
