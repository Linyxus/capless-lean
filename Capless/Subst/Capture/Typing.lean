import Capless.Subst.Basic
import Capless.Subst.Capture.Subtyping
import Capless.Typing
namespace Capless

theorem Typed.csubst
  {Γ : Context n m k} {Δ : Context n m k'}
  (h : Typed Γ t E)
  (σ : CVarSubst Γ f Δ) :
  Typed Δ (t.crename f) (E.crename f) := by
    induction h generalizing k'
    case var hb =>
      simp [Term.crename, EType.crename, CType.crename]
      have hb1 := σ.map _ _ hb
      simp [CType.crename] at hb1
      simp [CaptureSet.crename_singleton]
      apply Typed.var; trivial
    case pack ih =>
      simp [Term.crename, EType.crename]
      apply pack
      have ih := ih σ.cext
      simp [EType.crename] at ih
      exact ih
    case sub hs ih =>
      apply sub
      { apply ih; trivial }
      { apply hs.csubst; trivial }
    case abs hc ih =>
      simp [Term.crename, EType.crename, CType.crename, SType.crename]
      apply abs
      { apply ih
        apply σ.ext }
      { have hc1 := hc.crename (f := f)
        simp [Term.crename] at hc1
        exact hc1 }
    case tabs hc ih =>
      simp [Term.crename, EType.crename, CType.crename, SType.crename]
      apply tabs
      { apply ih
        apply σ.text }
      { have hc1 := hc.crename (f := f)
        simp [Term.crename] at hc1
        exact hc1 }
    case cabs hc ih =>
      simp [Term.crename, EType.crename, CType.crename, SType.crename]
      apply cabs
      { apply ih
        apply σ.cext }
      { have hc1 := hc.crename (f := f)
        simp [Term.crename] at hc1
        exact hc1 }
    case app ih1 ih2 =>
      simp [Term.crename]
      rw [EType.crename_open]
      apply app
      { have ih1 := ih1 σ
        simp [Term.crename, EType.crename, CType.crename, SType.crename] at ih1
        exact ih1 }
      { have ih2 := ih2 σ
        simp [Term.crename, EType.crename, CType.crename, SType.crename] at ih2
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
    case box ih =>
      simp [Term.crename, EType.crename, CType.crename, SType.crename]
      apply box
      have ih1 := ih σ
      simp [Term.crename, EType.crename, CType.crename, SType.crename] at ih1
      exact ih1
    case unbox ih =>
      simp [Term.crename, EType.crename, CType.crename, SType.crename]
      apply unbox
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
        exact ih2 }
    case letex ih1 ih2 =>
      simp [Term.crename]
      apply letex
      { have ih1 := ih1 σ
        simp [EType.crename] at ih1
        exact ih1 }
      { have ih2 := ih2 (σ.cext.ext _)
        rw [<-EType.weaken_crename] at ih2
        rw [<-EType.cweaken_crename] at ih2
        exact ih2 }
    case bindt ih =>
      simp [Term.crename]
      apply bindt
      have ih := ih σ.text
      rw [<-EType.tweaken_crename] at ih
      simp [TBinding.crename] at ih
      exact ih
    case bindc ih =>
      simp [Term.crename]
      apply bindc
      have ih := ih σ.cext
      rw [<-EType.cweaken_crename] at ih
      trivial

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
