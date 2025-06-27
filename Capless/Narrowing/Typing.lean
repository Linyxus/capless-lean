import Capless.Subst.Term.Typing
import Capless.Subst.Type.Typing
import Capless.Subst.Capture.Typing

/-!
# Narrowing Lemmas for Typing

This file establishes narrowing properties for the typing relation (`Typed`).
Narrowing allows strengthening the assumptions in typing contexts while preserving
typing judgments - a crucial property for modular reasoning about programs.

## Main Results

- `Typed.narrow`: Term variable narrowing - if `Γ,x:T ⊢ t : E ⊢ C` and `T' <: T`,
  then `Γ,x:T' ⊢ t : E ⊢ C`
- `Typed.tnarrow`: Type variable narrowing - if `Γ,X<:S ⊢ t : E ⊢ C` and `S' <: S`,
  then `Γ,X<:S' ⊢ t : E ⊢ C`
- `Typed.cnarrow`: Capture variable narrowing - if `Γ,c<:B ⊢ t : E ⊢ C` and `B' <: B`,
  then `Γ,c<:B' ⊢ t : E ⊢ C`

These lemmas demonstrate that typing is contravariant in assumption types - we can
always strengthen our assumptions about variables without affecting the conclusion.
The proofs utilize identity renamings combined with substitution lemmas.
-/

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
