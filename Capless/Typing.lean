import Capless.Context
import Capless.Subtyping
import Capless.Type
import Capless.Term

namespace Capless

inductive Finset.DropBinderFree : Finset (Fin (n+1)) -> Finset (Fin n) -> Prop where
| mk :
  Finset.DropBinderFree (Finset.image FinFun.weaken xs) xs

inductive Finset.DropBinder : Finset (Fin (n+1)) -> Finset (Fin n) -> Prop where
| drop_free :
  Finset.DropBinderFree xs ys ->
  Finset.DropBinder xs ys
| drop :
  Finset.DropBinderFree xs ys ->
  Finset.DropBinder (xs ∪ {0}) ys

inductive DropBinder : CaptureSet (n+1) k -> CaptureSet n k -> Prop where
| mk :
  Finset.DropBinder xs xs' ->
  DropBinder ⟨xs, cs⟩ ⟨xs', cs⟩

inductive DropBothBinder : CaptureSet (n+1) (k+1) -> CaptureSet n k -> Prop where
| mk :
  Finset.DropBinder xs xs' ->
  Finset.DropBinder ys ys' ->
  DropBothBinder ⟨xs, ys⟩ ⟨xs', ys'⟩

inductive DropCBinder : CaptureSet n (k+1) -> CaptureSet n k -> Prop where
| mk :
  DropCBinder C.cweaken C

inductive SealedLet : Term n m k -> CaptureSet (n+1) k -> Prop where
| mk :
  Term.IsValue t ->
  CaptureSet.NonLocal C2 ->
  SealedLet t C2

inductive Captured : Term n m k -> CaptureSet n k -> Prop where
| var :
  Captured (Term.var x) {x}
| lam :
  Captured t C ->
  DropBinder C C' ->
  Captured (Term.lam E t) C'
| tlam :
  Captured t C ->
  Captured (Term.tlam S t) C
| clam :
  Captured t C ->
  DropCBinder C C' ->
  Captured (Term.clam t) C'
| boxed :
  Captured (Term.boxed x) {}
| pack :
  Captured (Term.pack C x) {x}
| app :
  Captured (Term.app x y) ({x} ∪ {y})
| tapp :
  Captured (Term.tapp x S) {x}
| capp :
  Captured (Term.capp x c) {x}
| letin :
  Captured t1 C1 ->
  Captured t2 C2 ->
  ¬ (SealedLet t1 C2) ->
  DropBinder C2 C2' ->
  Captured (Term.letin t1 t2) (C1 ∪ C2')
| letin_sealed :
  Captured t1 C1 ->
  Captured t2 (CaptureSet.weaken C2) ->
  SealedLet t1 (CaptureSet.weaken C2) ->
  Captured (Term.letin t1 t2) C2
| letex :
  Captured t1 C1 ->
  Captured t2 C2 ->
  DropBothBinder C2 C2' ->
  Captured (Term.letex t1 t2) (C1 ∪ C2')
| unbox :
  Captured (Term.unbox C x) (C ∪ {x})

inductive Typed : Context n m k -> Term n m k -> EType n m k -> Prop where
| var :
  Context.Bound Γ x (CType.capt C S) ->
  Typed Γ (Term.var x) (EType.type (CType.capt {x} S))
| pack :
  Typed (Γ.cvar (CBinding.inst C)) (Term.var x) (EType.type T) ->
  Typed Γ (Term.pack C x) (EType.ex T)
| sub :
  Typed Γ t E1 ->
  ESubtyp Γ E1 E2 ->
  Typed Γ t E2
| abs :
  Typed (Context.var Γ E) t F ->
  Captured (Term.lam E t) C ->
  Typed Γ (Term.lam E t) (EType.type (CType.capt C (SType.forall E F)))
| tabs :
  Typed (Context.tvar Γ (TBinding.bound S)) t E ->
  Captured (Term.tlam S t) C ->
  Typed Γ (Term.tlam S t) (EType.type (CType.capt C (SType.tforall S E)))
| cabs :
  Typed (Context.cvar Γ CBinding.bound) t E ->
  Captured (Term.clam t) C ->
  Typed Γ (Term.clam t) (EType.type (CType.capt C (SType.cforall E)))
| app :
  Typed Γ (Term.var x) (EType.type (CType.capt C (SType.forall T F))) ->
  Typed Γ (Term.var y) (EType.type T) ->
  Typed Γ (Term.app x y) (F.open y)
| tapp :
  Typed Γ (Term.var x) (EType.type (CType.capt C (SType.tforall (SType.tvar X) E))) ->
  Typed Γ (Term.tapp x X) (E.topen X)
| capp :
  Typed Γ (Term.var x) (EType.type (CType.capt C (SType.cforall E))) ->
  Typed Γ (Term.capp x c) (E.copen c)
| box :
  Typed Γ (Term.var x) (EType.type T) ->
  Typed Γ (Term.boxed x) (EType.type (CType.capt {} (SType.box T)))
| unbox :
  Typed Γ (Term.var x) (EType.type (CType.capt {} (SType.box (CType.capt C S)))) ->
  Typed Γ (Term.unbox C x) (EType.type (CType.capt C S))
| letin :
  Typed Γ t1 (EType.type E1) ->
  Typed (Context.var Γ E1) t2 E2.weaken ->
  Typed Γ (Term.letin t1 t2) E2
| letex :
  Typed Γ t1 (EType.ex T1) ->
  Typed ((Γ.cvar CBinding.bound).var T1) t2 E2.cweaken.weaken ->
  Typed Γ (Term.letex t1 t2) E2
| bindt :
  Typed (Context.tvar Γ (TBinding.inst S)) t E.tweaken ->
  Typed Γ (Term.bindt S t) E
| bindc :
  Typed (Context.cvar Γ (CBinding.inst C)) t E.cweaken ->
  Typed Γ (Term.bindc C t) E

end Capless
