import Capless.Subst.Term.Subtyping
import Capless.Subst.Type.Subtyping
import Capless.Subst.Capture.Subtyping

/-!
# Narrowing Lemmas for Subtyping

This file provides narrowing lemmas for the expression subtyping relation (`ESubtyp`).
Narrowing is a fundamental property in type theory that states: if a judgment holds in a
context with a stronger assumption, then it also holds when that assumption is weakened
to a subtype.

## Main Results

- `ESubtyp.narrow`: Narrowing for term variable bindings - if `Γ,x:T ⊢ E1 <: E2` and `T' <: T`,
  then `Γ,x:T' ⊢ E1 <: E2`
- `ESubtyp.tnarrow`: Narrowing for type variable bindings - if `Γ,X<:S ⊢ E1 <: E2` and `S' <: S`,
  then `Γ,X<:S' ⊢ E1 <: E2`
- `ESubtyp.cnarrow`: Narrowing for capture variable bindings - if `Γ,c<:B ⊢ E1 <: E2` and `B' <: B`,
  then `Γ,c<:B' ⊢ E1 <: E2`

These lemmas are implemented using substitution with the identity renaming function,
showing that narrowing is a special case of substitution where we substitute variables
with themselves but in a strengthened context.
-/

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
