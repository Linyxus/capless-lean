import Capless.Subst.Term.Typing
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


end Capless
