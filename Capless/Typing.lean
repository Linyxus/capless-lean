import Capless.Context
import Capless.Subtyping
import Capless.Type
import Capless.Term

namespace Capless

inductive Typed : Context n m k -> Term n m k -> EType n m k -> CaptureSet n k -> Prop where
| var :
  Context.Bound Γ x (S^C) ->
  Typed Γ (Term.var x) (S^{x=x}) {}
| pack :
  Typed (Γ.cvar (CBinding.inst C)) (Term.var x) (EType.type T) Cx.cweaken ->
  Typed Γ (Term.pack C x) (∃c.T) Cx
| sub :
  Typed Γ t E1 C1 ->
  (Γ ⊢ C1 <:c C2) ->
  (Γ ⊢ E1 <:e E2) ->
  Typed Γ t E2 C2
| abs {C : CaptureSet n k} :
  Typed (Γ,x:T) t E C.weaken ->
  Typed Γ (λ(x:T)t) ((∀(x:T)E)^C) {}
| tabs {C : CaptureSet n k} :
  Typed (Γ,X<:S) t E C ->
  Typed Γ (λ[X<:S]t) ((∀[X<:S]E)^C) {}
| cabs {C : CaptureSet n k} :
  Typed (Γ,c:CapSet) t E C.cweaken ->
  Typed Γ (λ[c]t) ((∀[c]E)^C) {}
| box :
  Typed Γ (Term.var x) (EType.type T) {x=x} ->
  Typed Γ (Term.boxed x) ((SType.box T)^{}) {}
| app :
  Typed Γ (Term.var x) (EType.type (∀(x:T)E)^C) C' ->
  Typed Γ (Term.var y) T C' ->
  Typed Γ (Term.app x y) (E.open y) (C' ∪ C)
| tapp :
  Typed Γ (Term.var x) (EType.type (∀[X<:SType.tvar X]E)^C) C' ->
  Typed Γ (Term.tapp x X) (E.topen X) (C' ∪ C)
| capp :
  Typed Γ (Term.var x) (EType.type (∀[c]E)^C) C' ->
  Typed Γ (Term.capp x c) (E.copen c) (C' ∪ C)
| unbox :
  Typed Γ (Term.var x) (EType.type (SType.box (S^C))^{}) C' ->
  Typed Γ (C o- x) (S^C) (C' ∪ C)
| letin :
  Typed Γ t (EType.type T) C ->
  Typed (Γ,x: T) u E.weaken C.weaken ->  -- which means that x ∉ C and x ∉ fv(E)
  Typed Γ (let x=t in u) E C
| letex :
  Typed Γ t (EType.ex T) C ->
  Typed ((Γ,c:CapSet),x: T) u E.cweaken.weaken C.cweaken.weaken ->
  Typed Γ (let (c,x)=t in u) E C
| bindt :
  Typed (Γ,X:=S) t E.tweaken C ->
  Typed Γ (let X=S in t) E C
| bindc :
  Typed (Γ,c:=C) t E.cweaken C0.cweaken ->
  Typed Γ (let c=C in t) E C0

notation:40 C "; " Γ:80 " ⊢ " t " : " E => Typed Γ t E C

end Capless
