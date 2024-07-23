import Capless.Subtyping
import Capless.Subst.Basic
namespace Capless

theorem Typed.csubst
  (h : Typed Γ t E)
  (σ : CVarSubst Γ f Δ) :
  Typed Δ (t.crename f) (E.crename f) := by sorry

theorem Typed.copen
  (h : Typed (Γ.cvar CBinding.bound) t E) :
  Typed Γ (t.copen c) (E.copen c) := by
  simp [Term.copen, EType.copen]
  apply? Typed.csubst
  apply? CVarSubst.open

theorem Typed.cinstantiate {Γ : Context n m k}
  (h : Typed (Γ.cvar CBinding.bound) t E) :
  Typed (Γ.cvar (CBinding.inst C)) t E := by
  rw [<- Term.crename_id (t := t), <- EType.crename_id (E := E)]
  apply? Typed.csubst
  apply? CVarSubst.instantiate

theorem Typed.cinstantiate_extvar {Γ : Context n m k}
  (h : Typed ((Γ.cvar CBinding.bound).var P) t E) :
  Typed ((Γ.cvar (CBinding.inst C)).var P) t E := by
  rw [<- Term.crename_id (t := t), <- EType.crename_id (E := E)]
  apply? Typed.csubst
  conv =>
    arg 3
    rw [<- CType.crename_id (T := P)]
  apply CVarSubst.ext
  apply CVarSubst.instantiate

end Capless
