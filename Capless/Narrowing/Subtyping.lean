import Capless.Subst.Term.Subtyping
import Capless.Subst.Type.Subtyping
import Capless.Subst.Capture.Subtyping
namespace Capless

theorem ESubtyp.narrow
  (h : ESubtyp (Γ.var T) E1 E2)
  (hs : CSubtyp Γ T' T) :
  ESubtyp (Γ.var T') E1 E2 := by
  rw [<- EType.rename_id (E := E1), <- EType.rename_id (E := E2)]
  apply ESubtyp.subst
  { trivial }
  { apply VarSubst.narrow
    trivial }

theorem ESubtyp.tnarrow
  (h : ESubtyp (Γ.tvar (TBinding.bound S)) E1 E2)
  (hs : SSubtyp Γ S' S) :
  ESubtyp (Γ.tvar (TBinding.bound S')) E1 E2 := by
  rw [<- EType.trename_id (E := E1), <- EType.trename_id (E := E2)]
  apply? ESubtyp.tsubst
  { apply? TVarSubst.narrow }

theorem ESubtyp.cnarrow
  (h : ESubtyp (Γ,c<:B) E1 E2)
  (hs : Subbound Γ B' B) :
  ESubtyp (Γ,c<:B') E1 E2 := by
  rw [<- EType.crename_id (E := E1), <- EType.crename_id (E := E2)]
  apply ESubtyp.csubst
  { easy }
  { apply CVarSubst.narrow; easy }

end Capless
