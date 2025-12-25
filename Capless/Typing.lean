import Capless.Context
import Capless.Subtyping
import Capless.Type
import Capless.Term
import Capless.CaptureBound
import Capless.ReachSet

/-!
# Typing Rules of Capless

This defines the typing judgement `C; Γ ⊢ t: E` in Fig. 2, 5 and 6. Most rules correspond directly to the paper definitions, except for the `Typed.bindc` and `Typed.bindt` rules, which are for type and capture set bindings introduced in the mechanization.

Note that the rules for boundary/break extension are also included in this definition.
-/

namespace Capless

inductive Typed : Context n m k -> Term n m k -> EType n m k -> CaptureSet n k -> Prop where
| var :
  Context.Bound Γ x (S^C) ->
  Typed Γ (Term.var x) (S^{x=x|.top}) {x=x|.top}
| label :
  Context.LBound Γ x c S ->
  Typed Γ (Term.var x) (Label[S]^{x=x|.top}) {x=x|.top}
| pack :
  CaptureBound Γ C B ->
  Typed (Γ.cvar (CBinding.inst C)) (Term.var x) (EType.type T) {x=x|.top} ->
  Typed Γ (Term.pack C x) (∃[c<:B]T) {}
| sub :
  Typed Γ t E1 C1 ->
  (Γ ⊢ C1 <:c C2) ->
  (Γ ⊢ E1 <:e E2) ->
  Typed Γ t E2 C2
| abs {C : CaptureSet n k} :
  Typed (Γ,x:T) t E (C.weaken ∪ {x=0|.top}) ->
  Typed Γ (λ(x:T)t) ((∀(x:T)E)^C) {}
| tabs {C : CaptureSet n k} :
  Typed (Γ,X<:S) t E C ->
  Typed Γ (λ[X<:S]t) ((∀[X<:S]E)^C) {}
| cabs {C : CaptureSet n k} :
  Typed (Γ,c<:B) t E C.cweaken ->
  Typed Γ (λ[c<:B]t) ((∀[c<:B]E)^C) {}
| app :
  Typed Γ (Term.var x) (EType.type (∀(x:T)E)^C) {x=x|.top} ->
  Typed Γ (Term.var y) T {x=y|.top} ->
  Typed Γ (Term.app x y) (E.open y) ({x=x|.top} ∪ {x=y|.top})
| invoke :
  Typed Γ (Term.var x) (EType.type (Label[S])^C) {x=x|.top} ->
  Typed Γ (Term.var y) (S^{}) {x=y|.top} ->
  Typed Γ (Term.invoke x y) E ({x=x|.top} ∪ {x=y|.top})
| tapp :
  Typed Γ (Term.var x) (EType.type (∀[X<:SType.tvar X]E)^C) {x=x|.top} ->
  Typed Γ (Term.tapp x X) (E.topen X) {x=x|.top}
| capp :
  Typed Γ (Term.var x) (EType.type (∀[c<:CBound.upper {c=c|.top}]E)^C) {x=x|.top} ->
  Typed Γ (Term.capp x c) (E.copen c) {x=x|.top}
| letin :
  Typed Γ t (EType.type T) C ->
  Typed (Γ,x: T) u E.weaken C.weaken ->  -- which means that x ∉ C and x ∉ fv(E)
  Typed Γ (let x=t in u) E C
| letex :
  Typed Γ t (EType.ex B T) C ->
  Typed ((Γ,c<:B),x: T) u E.cweaken.weaken C.cweaken.weaken ->
  Typed Γ (let (c,x)=t in u) E C
| bindt :
  Typed (Γ,X:=S) t E.tweaken C ->
  Typed Γ (let X=S in t) E C
| bindc :
  Typed (Γ,c:=C) t E.cweaken C0.cweaken ->
  Typed Γ (let c=C in t) E C0
| boundary {Γ : Context n m k} {S : SType n m k} :
  c.Subclass .control ->
  Typed
    ((Γ,c<:CBound.kind (.node c [])),x: Label[S.cweaken]^{c=0|.top})
    t
    (S.cweaken.weaken^{}) (C.cweaken.weaken ∪ {c=0|.top} ∪ {x=0|.top}) ->
  Typed Γ (boundary[c]: S in t) (S^CaptureSet.empty) C
| intercept {Γ : Context n m k} {S : SType n m k} {C C1 Cr : CaptureSet n k}:
  Typed
    (((Γ,X<:.top),x:(Label[.tvar 0]^(Cr.proj K))),x:(SType.tvar 0)^{})
    h
    (S.tweaken.weaken.weaken^{}) (C1.weaken.weaken ∪ {x=0|.top} ∪ {x=1|.top}) ->
  Typed Γ t (S^{}) C ->
  ReachSet Γ C Cr' ->
  Cr' ⊆ Cr ->
  Typed Γ (intercept[K] with h in t) (S^{}) (C ∪ C1)
-- | unwrap {Γ : Context n m k} {S : SType n m k} :
--   Typed Γ (Term.var x) (EType.type (.maybe S)^C) {x=x|.top} ->
--   Typed Γ (.unwrap x t) (S^CaptureSet.empty) C
-- | ok {Γ : Context n m k} {S : SType n m k} :
--   Typed Γ (Term.var x) (S^CaptureSet.empty) {x=x|.top} -> Typed Γ (Term.ok x) ((SType.maybe S)^CaptureSet.empty) {x=x|.top}
-- | invoked {Γ : Context n m k} {S : SType n m k} :
--   Typed Γ (Term.var l) (Label[S]^C) {x=l|.top} ->
--   Typed Γ (Term.var v) (S^CaptureSet.empty) {x=v|.top} ->
--   Typed Γ (Term.invoked l v) ((SType.maybe S)^C) ({x=l|.top} ∪ {x=v|.top})

notation:40 Γ " ⊢ " t:80 " : " E " @ " C => Typed Γ t E C

end Capless
