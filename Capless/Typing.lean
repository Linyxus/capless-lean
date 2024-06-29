import Capless.Context
import Capless.Subtyping
import Capless.Type
import Capless.Term

namespace Capless

inductive DropBinderFree : CaptureSet (n+1) k -> CaptureSet n k -> Prop where
| mk :
  DropBinderFree C.weaken C

inductive DropBinder : CaptureSet (n+1) k -> CaptureSet n k -> Prop where
| drop_free :
  DropBinderFree C C' ->
  DropBinder C C'
| drop {C : CaptureSet n k}:
  DropBinder (C.weaken ∪ {0}) C

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
  Captured (Term.pack c x) {x}
| unpack :
  Captured (Term.unpack x) {x}
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
| unbox :
  Captured (Term.unbox C x) (C ∪ {x})

inductive Typed : Context n m k -> Term n m k -> EType n m k -> Prop where
| var :
  Context.Bound Γ x E ->
  Typed Γ (Term.var x) E
-- | exists_elim :
--   Typed Γ (Term.var x) (EType.ex (CType.capt C S)) ->
--   Context.CBound Γ c (CBinding.inst (CaptureSet.rsingleton x)) ->
--   Typed Γ (Term.var x) (EType.type (CType.capt {x} (S.copen c)))
| pack :
  Typed Γ (Term.var x) (EType.type (CType.copen T c0)) ->
  Typed Γ (Term.pack c0 x) (EType.exp c0 T)
| unpack :
  Typed Γ (Term.var x) (EType.ex (CType.capt C S)) ->
  Context.CBound Γ c (CBinding.inst (CaptureSet.rsingleton x)) ->
  Typed Γ (Term.unpack x) (EType.type (CType.capt {x} (S.copen c)))
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
  Typed Γ (Term.var x) (EType.type (CType.capt C (SType.forall E F))) ->
  Typed Γ (Term.var y) E ->
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
  Typed Γ t1 E1 ->
  Typed (Context.var Γ E1) T2 E2.weaken ->
  Typed Γ (Term.letin t1 t2) E2
| bindt :
  Typed (Context.tvar Γ (TBinding.inst S)) t E.tweaken ->
  Typed Γ (Term.bindt S t) E
| bindc :
  Typed (Context.cvar Γ (CBinding.inst C)) t E.cweaken ->
  Typed Γ (Term.bindc C t) E

end Capless
