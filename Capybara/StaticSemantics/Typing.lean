import Capybara.StaticSemantics.CaptureRoot
import Capybara.StaticSemantics.Chaining
import Capybara.StaticSemantics.Separation
import Capybara.StaticSemantics.Subtyping
import Capybara.StaticSemantics.Kinding
namespace Capybara

/-!
`RootDropped Γ C D` means that any capture root in `C` is dropped in `D`.
-/
def RootDropped (Γ : Context n m k) (C D : CaptureSet n k) : Prop :=
  ∀ m c, ReachRoot Γ C ⟨m,c⟩ -> (Γ ⊢c {c@drop:=c} <: D)

/-!
The typing relation.
-/
inductive Typed : CaptureSet n k -> Context n m k -> Term n m k -> EType n m k -> Prop where
| var :
  Γ.Lookup x (CType.capt C m S) ->
  Mutability.LessPermissive m' m ->
  --------------------------------
  Typed ({x@Mode.M m':=x}) Γ (Term.var x) (EType.type (CType.capt ({x:=x}) m' S))
| pack :
  Typed C' Γ (Term.var x) (EType.type (T.copen c)) ->
  RootDropped Γ ({c:=c}) C' ->
  Kinding Γ ({c:=c}) CKind.Fresh ->
  -----------------------------------------------------
  Typed C' Γ (Term.pack c x) (EType.ex T)
| subc :
  Typed C Γ t E ->
  (Γ ⊢c C <: C') ->
  -----------------------------------
  Typed C' Γ t E
| abs :
  Typed (C.weaken ∪ CaptureSet.span 0) (Γ,x:T) t E ->
  ------------------------------------------------------------
  Typed {} Γ (Term.lam T t) (EType.type (((x:T)->E)^[ε]C))
| tabs :
  Typed C (Γ,X:tparam S) t E ->
  ------------------------------------------------------------
  Typed C Γ (Term.tlam S t) (EType.type (([X<:S]->E)^[ε]C))
| cabs :
  Typed C.cweaken (Γ,c:cparam (CKind.Sep D)) t E ->
  ------------------------------------------------------------
  Typed C Γ (Term.clam D t) (EType.type (([c:D]->E)^[ε]C))
| fabs :
  Typed (C.cweaken.weaken ∪ CaptureSet.span 0) ((Γ,c:cparam CKind.Fresh),x:T) t E ->
  ------------------------------------------------------------
  Typed C Γ (Term.flam T t) (EType.type (([c:Fresh](x:T)->E)^[ε]C))
| app :
  Typed C' Γ (Term.var x) (EType.type (((x:T)->E)^[ε]Cf)) ->
  Typed C' Γ (Term.var y) (EType.type T0) ->
  (Γ ⊢ T0 <: T) ->
  Chaining Γ ({x:=x}) ({x:=y}) ->
  Chaining Γ ({x:=y}) ({x:=x}) ->
  ------------------------------------------------------------
  Typed C' Γ (Term.app x y) (E.open y)
| tapp :
  Typed C' Γ (Term.var x) (EType.type (([X<:S]->E)^[ε]Cf)) ->
  (Γ ⊢s (SType.tvar X) <: S) ->
  ------------------------------------------------------------
  Typed C' Γ (Term.tapp x X) (E.topen X)
| capp :
  Typed C' Γ (Term.var x) (EType.type (([c:D]->E)^[ε]Cf)) ->
  Kinding Γ ({c:=c}) (CKind.Sep D) ->
  ------------------------------------------------------------
  Typed C' Γ (Term.capp x c) (E.copen c)
| fapp :
  Typed C' Γ (Term.var x) (EType.type (([c:Fresh](x:T)->E)^[ε]Cf)) ->
  Typed C' Γ (Term.var y) (EType.type T0) ->
  (Γ ⊢ T0 <: (T.copen c)) ->
  RootDropped Γ ({c:=c}) C' ->
  Kinding Γ ({c:=c}) CKind.Fresh ->
  DroppedChaining Γ ({c:=c}) ({x:=x}) ->
  ------------------------------------------------------------
  Typed C' Γ (Term.fapp x c y) ((E.copen c).open y)


end Capybara
