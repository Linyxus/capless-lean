import Capless.Context
import Capless.Subtyping
import Capless.Type
import Capless.Term

namespace Capless

inductive Typed : Context n m k -> Term n m k -> EType n m k -> CaptureSet n k -> Prop where
| var :
  Context.Bound Γ x (S^C) ->
  Typed Γ (Term.var x) (S^{x=x}) {x=x}
| label :
  Context.LBound Γ x S ->
  Typed Γ (Term.var x) (Label[S]^{x=x}) {x=x}
| pack :
  Typed (Γ.cvar (CBinding.inst C)) (Term.var x) (EType.type T) {x=x} ->
  Typed Γ (Term.pack C x) (∃c.T) {x=x}
| sub :
  Typed Γ t E1 C1 ->
  (Γ ⊢ C1 <:c C2) ->
  (Γ ⊢ E1 <:e E2) ->
  Typed Γ t E2 C2
| abs {C : CaptureSet n k} :
  Typed (Γ,x:T) t E (C.weaken ∪ {x=0}) ->
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
  Typed Γ (Term.var x) (EType.type (∀(x:T)E)^C) {x=x} ->
  Typed Γ (Term.var y) T {x=y} ->
  Typed Γ (Term.app x y) (E.open y) ({x=x} ∪ {x=y})
| invoke :
  Typed Γ (Term.var x) (EType.type (Label[S])^C) {x=x} ->
  Typed Γ (Term.var y) (S^{}) {x=y} ->
  Typed Γ (Term.invoke x y) E ({x=x} ∪ {x=y})
| tapp :
  Typed Γ (Term.var x) (EType.type (∀[X<:SType.tvar X]E)^C) {x=x} ->
  Typed Γ (Term.tapp x X) (E.topen X) {x=x}
| capp :
  Typed Γ (Term.var x) (EType.type (∀[c]E)^C) {x=x} ->
  Typed Γ (Term.capp x c) (E.copen c) {x=x}
| unbox :
  Typed Γ (Term.var x) (EType.type (SType.box (S^C))^{}) {} ->
  Typed Γ (C o- x) (S^C) C
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
| boundary {Γ : Context n m k} {S : SType n m k} :
  Typed
    ((Γ,c:CapSet),x: Label[S.cweaken]^{c=0})
    t
    (S.cweaken.weaken^{}) (C.cweaken.weaken ∪ {c=0} ∪ {x=0}) ->
  Typed Γ (boundary: S in t) (S^CaptureSet.empty) C

notation:40 Γ " ⊢ " t:80 " : " E " @ " C => Typed Γ t E C

end Capless
