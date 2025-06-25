import Capless.Typing
import Capless.Renaming.Basic
import Capless.Renaming.Type.Subtyping

/-!
# Type Variable Renaming for Typing

This module proves that typing judgments are preserved under type variable renaming.
The main theorem `Typed.trename` shows that if `Γ ⊢ t : E @ Ct`, then after renaming
type variables with a valid renaming map, we have `Δ ⊢ t.trename f : E.trename f @ Ct`.
-/
namespace Capless

theorem Typed.trename
  {Γ : Context n m k} {Δ : Context n m' k}
  (h : Typed Γ t E Ct)
  (ρ : TVarMap Γ f Δ) :
  Typed Δ (t.trename f) (E.trename f) Ct := by
  induction h generalizing m'
  case var =>
    simp [Term.trename, EType.trename, CType.trename]
    apply var
    rename_i hb
    have hb1 := ρ.map _ _ hb
    simp [CType.trename] at hb1
    trivial
  case pack ih =>
    simp [Term.trename, EType.trename]
    apply pack
    have ih := ih (ρ.cext _)
    simp [Term.trename, EType.trename] at ih
    trivial
  case sub hsc hs ih =>
    apply sub
    aesop
    apply! hsc.trename
    apply! ESubtyp.trename
  case abs ih =>
    simp [Term.trename, EType.trename, CType.trename, SType.trename]
    apply abs
    apply? ih
    apply! TVarMap.ext
  case app ih1 ih2 =>
    simp [Term.trename]
    rw [EType.trename_open]
    apply app
    have ih1 := ih1 ρ
    simp [EType.trename, CType.trename, SType.trename, Term.trename] at ih1
    trivial
    have ih2 := ih2 ρ
    simp [Term.trename, EType.trename] at ih2
    trivial
  case tabs ih =>
    simp [Term.trename, EType.trename, CType.trename, SType.trename]
    apply tabs
    apply? ih
    apply! TVarMap.text
  case cabs ih =>
    simp [Term.trename, EType.trename, CType.trename, SType.trename]
    apply cabs
    have ih1 := ih (ρ.cext _)
    trivial
  case tapp ih =>
    simp [Term.trename]
    rw [EType.trename_topen]
    apply tapp
    have ih := ih ρ
    simp [Term.trename, EType.trename, CType.trename, SType.trename] at ih
    trivial
  case capp ih =>
    simp [Term.trename]
    rw [EType.trename_copen]
    apply capp
    have ih := ih ρ
    simp [Term.trename, EType.trename, CType.trename, SType.trename] at ih
    trivial
  case letin ih1 ih2 =>
    simp [Term.trename]
    apply letin
    simp [EType.trename] at ih1
    aesop
    have ih2 := ih2 (ρ.ext _)
    rw [<- EType.weaken_trename] at ih2
    trivial
  case letex ih1 ih2 =>
    simp [Term.trename]
    apply letex
    simp [EType.trename] at ih1
    aesop
    have ih2 := ih2 ((ρ.cext _).ext _)
    rw [<- EType.weaken_trename] at ih2
    rw [<- EType.cweaken_trename] at ih2
    trivial
  case bindt ih =>
    simp [Term.trename]
    apply bindt
    have ih := ih (ρ.text _)
    rw [EType.tweaken_trename]
    trivial
  case bindc ih =>
    simp [Term.trename]
    apply bindc
    have ih := ih (ρ.cext _)
    rw [EType.cweaken_trename]
    trivial
  case label =>
    simp [Term.trename, EType.trename, CType.trename, SType.trename]
    apply label
    have h := ρ.lmap
    aesop
  case invoke ih1 ih2 =>
    simp [Term.trename]
    apply invoke
    simp [Term.trename, EType.trename, CType.trename, SType.trename] at ih1
    apply ih1; trivial
    simp [Term.trename, EType.trename, CType.trename, SType.trename] at ih2
    apply ih2; trivial
  case boundary ih =>
    simp [Term.trename, EType.trename, CType.trename]
    apply boundary
    have ih := ih ((ρ.cext _).ext _)
    simp [FinFun.ext, CType.trename, SType.trename] at ih
    rw [ SType.cweaken_trename
       , SType.weaken_trename ]
    simp [EType.trename, CType.trename] at ih
    exact ih

end Capless
