import Capless.Subst.Term.Typing
namespace Capless

theorem Typed.narrow
  (h : Typed (Γ.var T) t E)
  (hs : CSubtyp Γ T' T) :
  Typed (Γ.var T') t E := by
  rw [<- EType.rename_id (E := E)]
  rw [<- Term.rename_id (t := t)]
  apply Typed.subst
  { exact h }
  { apply VarSubst.narrow
    trivial }


end Capless
