import Cappy.TypeSystem.Subtyping
import Cappy.Syntax.Term
namespace Cappy

mutual

inductive CType.CapRefine : CaptureSet n -> CType n m -> CType n m -> Prop where
| r_capt :
  SType.CapRefine D S S' ->
  CType.CapRefine D (S^C) (S'^(C.open_cap D))

inductive SType.CapRefine : CaptureSet n -> SType n m -> SType n m -> Prop where
| r_top :
  SType.CapRefine D top top
| r_tvar :
  SType.CapRefine D (SType.tvar X) (SType.tvar X)
| r_fun :
  CType.CapRefine (D.weaken ∪ {x=0} ∪ {x*=0}) U U' ->
  SType.CapRefine D (SType.arrow a T U) (SType.arrow a T U')
| r_tfun :
  CType.CapRefine D T T' ->
  SType.CapRefine D (SType.tarrow S T) (SType.tarrow S T')
| r_boxed :
  CType.CapRefine D T T' ->
  SType.CapRefine D (SType.boxed T) (SType.boxed T')

end

inductive Typed : CaptureSet n -> Context n m -> Term n m -> CType n m -> Prop where
| var :
  Γ.Bound x (S^C) ->
  S.CapRefine {x*=x} S' ->
  Typed {x=x} Γ (Term.var x) (S'^{x=x})
| sub :
  Typed C Γ t T ->
  Subcapt Γ C C' ->
  CSubtyp Γ T T' ->
  Typed C' Γ t T'
| abs {C : CaptureSet n} :
  Typed (C.weaken ∪ {x=0} ∪ {x*=0}) (Γ.var T) t U ->
  Typed {} Γ (Term.abs Annot.eps T t) ((∀(x:T)U)^C)
| uabs {C : CaptureSet n} :
  Typed (C.weaken ∪ {x=0}) (Γ.var T) t U ->
  Typed {} Γ (Term.abs Annot.use T t) ((∀(use x:T)U)^C)
| tabs {C : CaptureSet n} :
  Typed C (Γ.tvar S) t T ->
  Typed {} Γ (Term.tabs S t) ((∀[X<:S]T)^C)
| box {C : CaptureSet n} :
  Typed C Γ (Term.var x) T ->
  Typed {} Γ (Term.box x) ((SType.boxed T)^{})
| unbox {C : CaptureSet n} :
  Typed C Γ (Term.var x) ((SType.boxed (S^C))^{}) ->
  Typed C Γ (Term.unbox C x) (S^C)
| letin {C : CaptureSet n} {U : CType n m} :
  Typed C Γ t T ->
  Typed C.weaken (Γ.var T) u U.weaken ->
  Typed C Γ (Term.letin t u) U

end Cappy
