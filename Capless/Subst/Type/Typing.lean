import Capless.Subst.Basic
import Capless.Subst.Type.Subtyping
import Capless.Typing
namespace Capless

theorem Typed.tsubst
  {Γ : Context n m k} {Δ : Context n m' k}
  (h : Typed Γ t E Ct)
  (σ : TVarSubst Γ f Δ) :
  Typed Δ (t.trename f) (E.trename f) Ct := by
    induction h generalizing m'
    case var hb =>
      simp [Term.trename, EType.trename, CType.trename]
      have hb1 := σ.map _ _ hb
      simp [CType.trename] at hb1
      apply Typed.var; trivial
    case pack ih =>
      simp [Term.trename, EType.trename]
      apply pack
      have ih := ih σ.cext
      simp [EType.trename] at ih
      exact ih
    case sub hsc hs ih =>
      apply sub
      { apply ih; trivial }
      { apply! hsc.tsubst  }
      { apply! hs.tsubst }
    case abs ih =>
      simp [Term.trename, EType.trename, CType.trename, SType.trename]
      apply abs
      { apply ih
        apply σ.ext }
    case tabs ih =>
      simp [Term.trename, EType.trename, CType.trename, SType.trename]
      apply tabs
      { apply ih
        apply σ.text }
    case cabs ih =>
      simp [Term.trename, EType.trename, CType.trename, SType.trename]
      apply cabs
      { apply ih
        apply σ.cext }
    case app ih1 ih2 =>
      simp [Term.trename]
      rw [EType.trename_open]
      apply app
      { have ih1 := ih1 σ
        simp [Term.trename, EType.trename, CType.trename, SType.trename] at ih1
        exact ih1 }
      { have ih2 := ih2 σ
        simp [Term.trename, EType.trename, CType.trename, SType.trename] at ih2
        exact ih2 }
    case tapp ih =>
      simp [Term.trename]
      rw [EType.trename_topen]
      apply tapp
      have ih1 := ih σ
      simp [Term.trename, EType.trename, CType.trename, SType.trename] at ih1
      exact ih1
    case capp ih =>
      simp [Term.trename]
      rw [EType.trename_copen]
      apply capp
      have ih1 := ih σ
      simp [Term.trename, EType.trename, CType.trename, SType.trename] at ih1
      exact ih1
    case box ih =>
      simp [Term.trename, EType.trename, CType.trename, SType.trename]
      apply box
      have ih1 := ih σ
      simp [Term.trename, EType.trename, CType.trename, SType.trename] at ih1
      exact ih1
    case unbox ih =>
      simp [Term.trename, EType.trename, CType.trename, SType.trename]
      apply unbox
      have ih1 := ih σ
      simp [Term.trename, EType.trename, CType.trename, SType.trename] at ih1
      exact ih1
    case letin ih1 ih2 =>
      simp [Term.trename]
      apply letin
      { have ih1 := ih1 σ
        simp [EType.trename] at ih1
        exact ih1 }
      { have ih2 := ih2 (σ.ext _)
        rw [<- EType.weaken_trename] at ih2
        exact ih2 }
    case letex ih1 ih2 =>
      simp [Term.trename]
      apply letex
      { have ih1 := ih1 σ
        simp [EType.trename] at ih1
        exact ih1 }
      { have ih2 := ih2 (σ.cext.ext _)
        rw [<-EType.weaken_trename] at ih2
        rw [<-EType.cweaken_trename] at ih2
        exact ih2 }
    case bindt ih =>
      simp [Term.trename]
      apply bindt
      have ih := ih (σ.text _)
      rw [<-EType.tweaken_trename] at ih
      simp [TBinding.trename] at ih
      exact ih
    case bindc ih =>
      simp [Term.trename]
      apply bindc
      have ih := ih σ.cext
      rw [<-EType.cweaken_trename] at ih
      trivial
    case label hb =>
      simp [Term.trename, EType.trename, CType.trename, SType.trename]
      have hb1 := σ.lmap _ _ hb
      apply label; assumption
    case invoke ih1 ih2 =>
      simp [Term.trename]
      apply invoke
      apply ih1; assumption
      apply ih2; assumption
    case boundary ih =>
      simp [Term.trename]
      apply boundary
      have ih := ih (σ.cext.ext _)
      simp [CType.trename, SType.trename] at ih
      rw [ <- SType.cweaken_trename
         , <- EType.weaken_trename
         , <- EType.cweaken_trename ] at ih
      aesop

theorem Typed.tnarrow
  (h : Typed (Γ,X<: S) t E Ct)
  (hs : SSubtyp Γ S' S) :
  Typed (Γ,X<: S') t E Ct := by
  rw [<- Term.trename_id (t := t), <- EType.trename_id (E := E)]
  apply? Typed.tsubst
  apply? TVarSubst.narrow

theorem Typed.topen
  (h : Typed (Γ,X<: (SType.tvar X)) t E Ct) :
  Typed Γ (t.topen X) (E.topen X) Ct := by
  apply? Typed.tsubst
  apply? TVarSubst.open

end Capless
