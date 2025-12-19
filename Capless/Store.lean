import Capless.Term
import Capless.Type
import Capless.CaptureSet
import Capless.Context
import Capless.Typing

/-!
# Evaluation States

This module defines the evaluation states in System Capless.

`Store n m k` defines the store (Fig. 1). It is indexed by the number of term, type and capture bindings in the store.
- `Store.empty` and `Store.val` corresponds directly to the paper definition.
- `Store.tval` and `Store.cval` are for type and capture set bindings bound by `Term.bindt` and `Term.bindc`. During evaluation, `Term.bindt` and `Term.bindc` are lifted as `Store.tval` and `Store.cval` bindings in the store.
- `Store.label` declares a label in the store.

`Cont n m k` defines a continuation stack that is valid in a store `Store n m k`. On the paper, the evaluation state is defined as a pair of a store and a term, `⟨σ | t⟩`. `t` is then decomposed into a evaluation context and a redex `t = e[u]`. In the mechanization, we define evaluation state `State n m k` as a triplet of a store, a continuation stack and the redex, `⟨σ | cont | t⟩`. The continuation stack corresponds to the evaluation context.
-/

namespace Capless

/-- Store. -/
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
  Classifier ->
  SType n m k ->
  Store (n+1) m k

/-- Continuation stack. -/
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
| intercept : -- intercept frame
  Kind ->
  Term (n + 2) (m + 1) k ->
  Cont n m k ->
  Cont n m k

/-- Evaluation state. -/
structure State (n : Nat) (m : Nat) (k : Nat) where
  σ : Store n m k
  cont : Cont n m k
  t : Term n m k

notation:max "⟨" σ " | " cont " | " t "⟩" => State.mk σ cont t

/-- Store Typing (Fig. 11). Note that the definition here is extended with the forms in the scoped capability extension. -/
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
  TypedStore (Store.label σ c S) (Γ.label c S)

/-- Checks whether a label is in the scope of a continuation stack. This corresponds to the paper definition of finding whether there exists a `scope` form for that label in the evaluation context, like in the (BREAKOUT) rule of Fig. 6.
 -/
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
| there_intercept :
  Cont.HasLabel cont l tail ->
  Cont.HasLabel (Cont.intercept K h cont) l tail

/-- Checks whether a label can be handled in an intercept scope of a continuation stack.
 -  We need to actually check the classifier here to see if they match. -/
inductive Cont.HasIntercept : Cont n m k -> Fin n -> Kind -> Option (Term (n + 2) (m + 1) k) -> Cont n m k -> Prop where
| here_label :
  Cont.HasIntercept (Cont.scope l tail) l L .none tail
| here_intercept :
  Cont.HasLabel tail l tail' -> -- the tail must actually contain the label frame
  L.disjoint K = false ->
  Cont.HasIntercept (Cont.intercept K h tail) l L (.some h) tail
| there_intercept :
  Cont.HasIntercept tail l L h' tail' ->
  L.disjoint K = true ->
  Cont.HasIntercept (Cont.intercept K h tail) l L h' tail'
| there_val :
  Cont.HasIntercept cont l L h tail ->
  Cont.HasIntercept (Cont.cons t cont) l L h tail
| there_tval :
  Cont.HasIntercept cont l L h tail ->
  Cont.HasIntercept (Cont.conse t cont) l L h tail
| there_cval :
  Cont.HasIntercept cont l L h tail ->
  Cont.HasIntercept (Cont.scope l' cont) l L h tail
| there_label :
  Cont.HasIntercept cont l L h tail ->
  Cont.HasIntercept (Cont.scope l' cont) l L h tail

theorem Cont.HasIntercept.has_label (hi : HasIntercept cont l L h tail) : ∃ tail', HasLabel cont l tail' := by
  induction hi
  case here_label l tail L => exists tail; apply HasLabel.here
  case here_intercept _ _ tail' _ _ _ hl _ => exists tail'; apply HasLabel.there_intercept hl
  case there_intercept ih =>
    have ⟨t, h⟩ := ih
    exists t; apply HasLabel.there_intercept h
  case there_val ih =>
    have ⟨t, h⟩ := ih
    exists t; apply HasLabel.there_val h
  case there_tval ih =>
    have ⟨t, h⟩ := ih
    exists t; apply HasLabel.there_tval h
  case there_cval ih =>
    have ⟨t, h⟩ := ih
    exists t; apply HasLabel.there_cval h
  case there_label ih =>
    have ⟨t, h⟩ := ih
    exists t; apply HasLabel.there_label h

theorem Cont.HasLabel.has_intercept (hl : HasLabel cont l tail) : ∃ h tail', HasIntercept cont l L h tail' := by
  induction hl
  case here l tail => exists .none, tail; apply! HasIntercept.here_label
  case there_val ih => have ⟨h, tail, ih⟩ := ih; exists h, tail; apply! HasIntercept.there_val
  case there_tval ih => have ⟨h, tail, ih⟩ := ih; exists h, tail; apply! HasIntercept.there_tval
  case there_cval ih => have ⟨h, tail, ih⟩ := ih; exists h, tail; apply! HasIntercept.there_cval
  case there_label ih => have ⟨h, tail, ih⟩ := ih; exists h, tail; apply! HasIntercept.there_label
  case there_intercept cont _ _ K h0 hl ih =>
    have ⟨h, tail, ih⟩ := ih
    generalize hd : L.disjoint K = b0
    cases b0
    . exists .some h0, cont; apply HasIntercept.here_intercept hl hd;
    . exists h, tail; apply! HasIntercept.there_intercept

/-- Computes the reach set of a capture set. The reach set should only consist of capture variables and -/
inductive ReachSet : Context n m k -> CaptureSet n k -> CaptureSet n k -> Prop where
| empty : ReachSet Γ .empty .empty
| union :
  ReachSet Γ C1 R1 ->
  ReachSet Γ C2 R2 ->
  ReachSet Γ (C1 ∪ C2) (R1 ∪ R2)
| var :
  Context.Bound Γ x (S^C) ->
  ReachSet Γ (C.proj L) R ->
  ReachSet Γ {x=x|L} R
| cinstr :
  Context.CBound Γ c (CBinding.inst C) ->
  ReachSet Γ (C.proj L) R ->
  ReachSet Γ {c=c|L} R
| cbound :
  Context.CBound Γ c (CBinding.bound (CBound.upper C)) ->
  ReachSet Γ (C.proj L) R ->
  ReachSet Γ {c=c|L} R
| ckind :
  Context.CBound Γ c (CBinding.bound (CBound.kind K)) ->
  ReachSet Γ {c=c|L} {c=c|L}
| label :
  Context.LBound Γ x c S ->
  ReachSet Γ {x=x|L} {x=x|L}

/-- Checks whether a capture set is well-scoped under a context and a continuation stack.
 -- A capture set is well-scoped if any label transitively reachable from it is in the scope of the continuation stack (via `Cont.HasLabel`).
 -- This is an invariant to be maintained thoroughout evaluation. -/
inductive WellScoped : Context n m k -> Cont n m k -> CaptureSet n k -> Prop where
| empty :
  WellScoped Γ cont {}
| union :
  WellScoped Γ cont C1 ->
  WellScoped Γ cont C2 ->
  WellScoped Γ cont (.union C1 C2)
| ckind :
  Context.CBound Γ c (CBinding.bound (CBound.kind K)) ->
  WellScoped Γ cont {c=c|L}
| label :
  Context.LBound Γ x c S ->
  Cont.HasLabel cont x tail ->
  WellScoped Γ cont {x=x|L}
| label_disj : -- label is within context but not reachable from stack
  Context.LBound Γ x c S ->
  Kind.Disjoint L (.classifier c) ->
  WellScoped Γ cont {x=x|L}

/-- Typecheck a continuation stack. `TypedCont Γ Ein cont Eout C` means that threading a input of type `Ein` with ambiant captures `Cin`
    through the continuation stack results in an output of type `Eout`,
    and the captured variables of the entire stack is `C`. -/
inductive TypedCont : Context n m k -> EType n m k -> CaptureSet n k -> Cont n m k -> EType n m k -> CaptureSet n k -> Prop where
| none :
  ESubtyp Γ E E' ->
  TypedCont Γ E Cin Cont.none E' {}
| cons {Ct : CaptureSet n k} :
  Typed (Γ,x: T) t (EType.weaken E) Ct.weaken ->
  WellScoped Γ cont Ct ->
  TypedCont Γ E (Cin ∪ Ct) cont E' C ->
  TypedCont Γ (EType.type T) Cin (Cont.cons t cont) E' (C ∪ Ct)
| conse {Ct : CaptureSet n k} :
  Typed ((Γ.cvar (CBinding.bound B)).var T) t (EType.weaken (EType.cweaken E)) Ct.cweaken.weaken ->
  WellScoped Γ cont Ct ->
  TypedCont Γ E (Cin ∪ Ct) cont E' C ->
  TypedCont Γ (EType.ex B T) Cin (Cont.conse t cont) E' (C ∪ Ct)
| scope :
  Context.LBound Γ x c S ->
  TypedCont Γ (S^{}) Cin cont E' C ->
  (Γ ⊢ T0 <: S^{}) ->
  TypedCont Γ (EType.type T0) Cin (Cont.scope x cont) E' C
| intercept {S : SType n m k} {Cin Ct: CaptureSet n k}:
  Typed (((Γ,X<:⊤),x:(Label[.tvar 0]^(Cin.proj K))),x:(SType.tvar 0)^{}) h (S.tweaken.weaken.weaken^CaptureSet.empty) (Ct.weaken.weaken ∪ {x=0|.top} ∪ {x=1|.top}) ->
  WellScoped Γ cont Ct ->
  TypedCont Γ (S^CaptureSet.empty) (Cin ∪ Ct) cont E' C ->
  (Γ ⊢ T0 <: (CType.capt .empty S)) ->
  TypedCont Γ (EType.type T0) Cin (Cont.intercept K h cont) E' (C ∪ Ct)


/-- Typecheck an evaluation state. -/
inductive TypedState : State n m k -> Context n m k -> EType n m k -> CaptureSet n k -> Prop where
| mk :
  TypedStore σ Γ ->
  Typed Γ t E Ct ->
  ReachSet Γ Ct Rt ->
  WellScoped Γ cont Rt ->
  TypedCont Γ E Ct cont E' C ->
  TypedState (State.mk σ cont t) Γ E' Rt

/-!
## Store Lookup

The following definitions look up bindings in the store.
-/

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
  Store.Bound (Store.label σ c S) (Fin.succ x) t.weaken

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
  Store.TBound (Store.label σ c S') x S.weaken

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
  Store.CBound (Store.label σ c S) x C.weaken

inductive Store.LBound : Store n m k -> (Fin n) -> Classifier -> SType n m k -> Prop where
| here :
  Store.LBound (Store.label σ c S) 0 c S.weaken
| there_val :
  Store.LBound σ x c S ->
  Store.LBound (Store.val σ t hv) x.succ c S.weaken
| there_tval :
  Store.LBound σ x c S ->
  Store.LBound (Store.tval σ S') x c S.tweaken
| there_cval :
  Store.LBound σ x c S ->
  Store.LBound (Store.cval σ C) x c S.cweaken
| there_label :
  Store.LBound σ x c S ->
  Store.LBound (Store.label σ c' S') x.succ c S.weaken

/-!
## Weakening of Continuation Stack

Weakning each frame in the continuation stack. It is used when a new binding is lifted to the store.
-/

def Cont.weaken : Cont n m k -> Cont (n+1) m k
| Cont.none => Cont.none
| Cont.cons t cont => Cont.cons t.weaken1 cont.weaken
| Cont.conse t cont => Cont.conse t.weaken1 cont.weaken
| Cont.scope x cont => Cont.scope x.succ cont.weaken
| Cont.intercept K h cont => Cont.intercept K (h.rename FinFun.weaken.ext.ext) cont.weaken

def Cont.tweaken : Cont n m k -> Cont n (m+1) k
| Cont.none => Cont.none
| Cont.cons t cont => Cont.cons t.tweaken cont.tweaken
| Cont.conse t cont => Cont.conse t.tweaken cont.tweaken
| Cont.scope x cont => Cont.scope x cont.tweaken
| Cont.intercept K h cont => Cont.intercept K (h.trename FinFun.weaken.ext) cont.tweaken

def Cont.cweaken : Cont n m k -> Cont n m (k+1)
| Cont.none => Cont.none
| Cont.cons t cont => Cont.cons t.cweaken cont.cweaken
| Cont.conse t cont => Cont.conse t.cweaken1 cont.cweaken
| Cont.scope x cont => Cont.scope x cont.cweaken
| Cont.intercept K h cont => Cont.intercept K h.cweaken cont.cweaken

/-!
## Tightness
-/

/-- A typing context is tight if it contains only term bindings and instance type/capture bindings. -/
@[aesop safe [constructors]]
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
  Context.IsTight (Γ.label c S)

/-- The typing context of a store is always tight. -/
theorem TypedStore.is_tight
  (h : TypedStore σ Γ) :
  Γ.IsTight := by
  induction h <;> aesop

end Capless
