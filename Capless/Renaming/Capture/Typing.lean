import Capless.Typing
import Capless.Renaming.Basic
import Capless.Renaming.Capture.Subtyping
namespace Capless

theorem Typed.crename
  {Γ : Context n m k} {Δ : Context n m k'}
  (h : Typed Γ t E Ct)
  (ρ : CVarMap Γ f Δ) :
  Typed Δ (t.crename f) (E.crename f) (Ct.crename f) := by
  induction h generalizing k'
  case var hb =>
    simp [Term.crename, EType.crename, CType.crename]
    apply var
    have hb1 := ρ.map _ _ hb
    simp [CType.crename] at hb1
    exact hb1
  case pack ih =>
    simp [Term.crename, EType.crename]
    apply pack
    have ih := ih (ρ.cext _)
    simp [Term.crename, EType.crename] at ih
    exact ih
  case sub hsc hsub ih =>
    apply sub
    apply ih ρ
    apply! hsc.crename
    apply! ESubtyp.crename hsub
  case abs ih =>
    simp [Term.crename, EType.crename, CType.crename, SType.crename]
    apply abs
    rw [CaptureSet.weaken_crename]
    apply ih
    apply ρ.ext
  case tabs hc ih =>
    simp [Term.crename, EType.crename, CType.crename, SType.crename]
    apply tabs
    apply ih
    apply ρ.text
  case cabs hc ih =>
    simp [Term.crename, EType.crename, CType.crename, SType.crename]
    apply cabs
    rw [CaptureSet.cweaken_crename]
    apply ih
    apply ρ.cext
  case app ih1 ih2 =>
    simp [Term.crename, EType.crename_open]
    apply app
    have ih1 := ih1 ρ
    simp [Term.crename, EType.crename, CType.crename, SType.crename] at ih1
    exact ih1
    have ih2 := ih2 ρ
    simp [Term.crename, EType.crename, CType.crename, SType.crename] at ih2
    exact ih2
  case tapp ih1 =>
    simp [Term.crename, EType.crename_topen]
    apply tapp
    have ih1 := ih1 ρ
    simp [Term.crename, EType.crename, CType.crename, SType.crename] at ih1
    exact ih1
  case capp ih1 =>
    simp [Term.crename, EType.crename_copen]
    apply capp
    have ih1 := ih1 ρ
    simp [Term.crename, EType.crename, CType.crename, SType.crename] at ih1
    exact ih1
  case box ih =>
    simp [Term.crename, EType.crename, CType.crename, SType.crename, CaptureSet.crename_empty]
    apply box
    have ih := ih ρ
    simp [Term.crename, EType.crename, CType.crename, SType.crename] at ih
    exact ih
  case unbox ih =>
    simp [Term.crename, EType.crename, CType.crename, SType.crename]
    apply unbox
    have ih := ih ρ
    simp [Term.crename, EType.crename, CType.crename, SType.crename] at ih
    exact ih
  case letin ih1 ih2 =>
    simp [Term.crename]
    apply letin
    have ih1 := ih1 ρ
    simp [EType.crename] at ih1
    exact ih1
    have ih2 := ih2 (ρ.ext _)
    rw [<- EType.weaken_crename] at ih2
    rw [CaptureSet.weaken_crename]
    exact ih2
  case letex ih1 ih2 =>
    simp [Term.crename]
    apply letex
    have ih1 := ih1 ρ
    simp [EType.crename] at ih1
    exact ih1
    have ih2 := ih2 ((ρ.cext _).ext _)
    rw [EType.cweaken_crename]
    rw [EType.weaken_crename]
    rw [CaptureSet.cweaken_crename, CaptureSet.weaken_crename]
    exact ih2
  case bindt ih =>
    simp [Term.crename]
    apply bindt
    have ih := ih (ρ.text _)
    rw [<- EType.tweaken_crename] at ih
    exact ih
  case bindc ih =>
    simp [Term.crename]
    apply bindc
    have ih := ih (ρ.cext _)
    rw [<- EType.cweaken_crename] at ih
    rw [CaptureSet.cweaken_crename]
    exact ih
  case label =>
    simp [Term.crename, EType.crename, CType.crename, SType.crename]
    apply label
    have h := ρ.lmap
    aesop
  case invoke ih1 ih2 =>
    simp [Term.crename]
    apply invoke
    apply ih1 <;> assumption
    apply ih2; assumption
  case boundary ih =>
    simp [Term.crename]
    apply boundary
    have ih := ih ((ρ.cext _).ext _)
    simp [CBinding.crename,
          TBinding.crename,
          CType.crename, EType.crename,
          FinFun.ext,
          SType.crename] at ih
    rw [<- SType.cweaken_crename,
        <- SType.weaken_crename,
        <- SType.cweaken_crename,
        <- CaptureSet.weaken_crename,
        <- CaptureSet.cweaken_crename] at ih
    exact ih

end Capless
