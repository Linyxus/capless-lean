import Capless.Subst.Term.Typing
import Capless.Subst.Type.Typing
import Capless.Subst.Capture.Typing
namespace Capless

theorem Typed.narrow
  (h : Typed (Γ,x: T) t E Ct)
  (hs : CSubtyp Γ T' T) :
  Typed (Γ,x: T') t E Ct := by
  rw [<- EType.rename_id (E := E)]
  rw [<- Term.rename_id (t := t)]
  rw [<- CaptureSet.rename_id (C := Ct)]
  apply Typed.subst
  { exact h }
  { apply VarSubst.narrow
    trivial }

theorem Typed.tnarrow
  (h : Typed (Γ,X<: S) t E Ct)
  (hs : SSubtyp Γ S' S) :
  Typed (Γ,X<: S') t E Ct := by
  rw [<- Term.trename_id (t := t), <- EType.trename_id (E := E)]
  apply? Typed.tsubst
  apply? TVarSubst.narrow

theorem Typed.cnarrow
  (h : Typed (Γ,c<:B) t E Ct)
  (hs : Subbound Γ B' B) :
  Typed (Γ,c<:B') t E Ct := by
  rw [<- Term.crename_id (t := t),
      <- EType.crename_id (E := E),
      <- CaptureSet.crename_id (C := Ct)]
  apply? Typed.csubst
  apply! CVarSubst.narrow

end Capless
