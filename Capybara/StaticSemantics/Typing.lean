import Capybara.StaticSemantics.CaptureRoot
import Capybara.StaticSemantics.Chaining
import Capybara.StaticSemantics.Separation
import Capybara.StaticSemantics.Subtyping
import Capybara.StaticSemantics.Kinding
namespace Capybara

inductive Typed : CaptureSet n k -> Context n m k -> Term n m k -> EType n m k -> Prop where
| var :
  Γ.Lookup x (CType.capt C m S) ->
  LessPermissive m' m ->
  --------------------------------
  Typed ({x@Mode.M m':=x}) Γ (Term.var x) (EType.type (CType.capt ({x:=x}) m' S))
| pack :
  Typed C' Γ (Term.var x) (EType.type (T.copen c)) ->
  CaptureSet.Root ({c:=c}) Γ R ->
  CaptureRoot.Kinding Γ R Kind.Fresh ->
  CaptureRoot.Dropped R C' ->
  -----------------------------------------------------
  Typed C' Γ (Term.pack c x) (EType.ex T)
| sub :
  Typed C Γ t E ->
  (Γ ⊢c C <: C') ->
  (Γ ⊢e E <: E') ->
  --------------------------------
  Typed C' Γ t E'
| abs :
  Typed (C.weaken ∪ CaptureSet.span x) (Γ,x:T) t E ->
  --------------------------------
  Typed {} Γ (Term.lam T t) (EType.type (((x:T)->E)^[ε]C))
| tabs :
  Typed C (Γ,X:tparam S) t E ->
  --------------------------------
  Typed C Γ (Term.tlam S t) (EType.type (([X<:S]->E)^[ε]C))

end Capybara
