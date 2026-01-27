import Capless.Subst.Basic
import Capless.Subst.Capture.Subtyping
import Capless.Subst.Capture.CaptureBound
import Capless.Typing
import Capless.WellScoped.Basic

/-
Substitution theorems for capture variable substitution in typing judgments.
-/

namespace Capless

theorem Typed.csubst
  {Γ : Context n m k} {Δ : Context n m k'}
  (h : Typed Γ t E Ct)
  (σ : CVarSubst Γ f Δ) :
  Typed Δ (t.crename f) (E.crename f) (Ct.crename f) := by
    induction h generalizing k'
    case var hb =>
      simp [Term.crename, EType.crename, CType.crename]
      have hb1 := σ.map _ _ hb
      simp [CType.crename] at hb1
      apply Typed.var; trivial
    case pack hb _ ih =>
      simp [Term.crename, EType.crename]
      apply pack (hb.csubst σ)
      have ih := ih σ.cext
      simp [EType.crename] at ih
      exact ih
    case sub hsc hs ih =>
      apply sub
      { apply ih; trivial }
      { apply! hsc.csubst }
      { apply! hs.csubst }
    case abs ih =>
      simp [Term.crename, EType.crename, CType.crename, SType.crename]
      apply abs
      { rw [CaptureSet.weaken_crename]
        apply ih
        apply σ.ext }
    case tabs ih =>
      simp [Term.crename, EType.crename, CType.crename, SType.crename]
      apply tabs
      { apply ih
        apply σ.text }
    case cabs ih =>
      simp [Term.crename, EType.crename, CType.crename, SType.crename]
      apply cabs
      { rw [CaptureSet.cweaken_crename]
        apply ih
        apply σ.cext }
    case app ih1 ih2 =>
      simp [Term.crename]
      rw [EType.crename_open]
      apply app
      { have ih1 := ih1 σ
        simp [Term.crename, EType.crename, CType.crename, SType.crename] at ih1
        exact ih1 }
      { have ih2 := ih2 σ
        simp [Term.crename, EType.crename] at ih2
        exact ih2 }
    case tapp ih =>
      simp [Term.crename]
      rw [EType.crename_topen]
      apply tapp
      have ih1 := ih σ
      simp [Term.crename, EType.crename, CType.crename, SType.crename] at ih1
      exact ih1
    case capp ih =>
      simp [Term.crename]
      rw [EType.crename_copen]
      apply capp
      have ih1 := ih σ
      simp [Term.crename, EType.crename, CType.crename, SType.crename] at ih1
      exact ih1
    case letin ih1 ih2 =>
      simp [Term.crename]
      apply letin
      { have ih1 := ih1 σ
        simp [EType.crename] at ih1
        exact ih1 }
      { have ih2 := ih2 (σ.ext _)
        rw [<- EType.weaken_crename] at ih2
        rw [CaptureSet.weaken_crename]
        exact ih2 }
    case letex ih1 ih2 =>
      simp [Term.crename]
      apply letex
      { have ih1 := ih1 σ
        simp [EType.crename] at ih1
        exact ih1 }
      { have ih2 := ih2 (σ.cext.ext _)
        rw [<- EType.weaken_crename] at ih2
        rw [<- EType.cweaken_crename] at ih2
        rw [CaptureSet.cweaken_crename]
        rw [CaptureSet.weaken_crename]
        exact ih2 }
    case bindt ih =>
      simp [Term.crename]
      apply bindt
      have ih := ih σ.text
      rw [<- EType.tweaken_crename] at ih
      simp [TBinding.crename] at ih
      exact ih
    case bindc ih =>
      simp [Term.crename]
      apply bindc
      have ih := ih σ.cext
      rw [<- EType.cweaken_crename] at ih
      rw [CaptureSet.cweaken_crename]
      trivial
    case label =>
      simp [Term.crename, EType.crename, CType.crename, SType.crename]
      apply label
      have h := σ.lmap
      aesop
    case invoke ih1 ih2 =>
      simp [Term.crename]
      simp [EType.crename, CType.crename, SType.crename] at ih1 ih2
      apply invoke
      apply ih1; assumption
      apply ih2; assumption
    case boundary ih =>
      simp [Term.crename]
      simp [EType.crename, CType.crename]
      apply boundary; assumption
      have ih := ih (σ.cext.ext _)
      simp [CBinding.crename, EType.crename, CType.crename, SType.crename, FinFun.ext] at ih
      rw [ <- SType.cweaken_crename
         , <- SType.weaken_crename
         , <- SType.cweaken_crename
         , <- CaptureSet.weaken_crename
         , <- CaptureSet.cweaken_crename ] at ih
      aesop
    case intercept hr hs ih ih2 =>
      simp [Term.crename]
      have ⟨R1, hrs1, hr1⟩ := hr.csubst σ
      apply intercept _ _ hr1 (CaptureSet.Subset.trans hrs1 hs.crename)
      have ih := ih $ (σ.text.ext _).ext _
      simp [TBinding.crename, EType.crename, CType.crename, SType.crename] at ih ih2
      simp [← SType.weaken_crename, ← SType.tweaken_crename, ← CaptureSet.weaken_crename, CaptureSet.proj_crename] at ih ih2
      apply ih
      apply! ih2


theorem Typed.copen
  (h : Typed (Γ,c<:CBound.upper {c=c|.top}) t E Ct) :
  Typed Γ (t.copen c) (E.copen c) (Ct.copen c) := by
  simp [Term.copen, EType.copen]
  apply? Typed.csubst
  apply? CVarSubst.open

theorem Typed.cinstantiate {Γ : Context n m k}
  (h : Typed (Γ,c<:B) t E Ct)
  (hb: CaptureBound Γ C B) :
  Typed (Γ,c:= C) t E Ct := by
  rw [<- Term.crename_id (t := t), <- EType.crename_id (E := E)]
  rw [<- CaptureSet.crename_id (C := Ct)]
  apply? Typed.csubst
  apply? CVarSubst.instantiate

theorem Typed.cinstantiate_extvar {Γ : Context n m k}
  (h : Typed ((Γ,c<:B).var P) t E Ct)
  (hb: CaptureBound Γ C B) :
  Typed ((Γ,c:=C).var P) t E Ct := by
  rw [<- Term.crename_id (t := t), <- EType.crename_id (E := E)]
  rw [<- CaptureSet.crename_id (C := Ct)]
  apply? Typed.csubst
  conv =>
    arg 3
    rw [<- CType.crename_id (T := P)]
  apply CVarSubst.ext
  apply? CVarSubst.instantiate

end Capless
