import Capybara.StaticSemantics.CaptureRoot
import Capybara.StaticSemantics.Chaining
import Capybara.StaticSemantics.Separation
import Capybara.StaticSemantics.Subtyping
namespace Capybara

inductive Typed : CaptureSet n k -> Context n m k -> Term n m k -> EType n m k -> Prop where
| var :
  Γ.Lookup x (CType.capt C m S) ->
  LessPermissive m' m ->
  --------------------------------
  Typed ({x@Mode.M m':=x}) Γ (Term.var x) (EType.type (CType.capt ({x:=x}) m' S))

end Capybara
