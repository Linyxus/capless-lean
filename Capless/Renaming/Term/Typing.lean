import Capless.Typing
import Capless.Renaming.Basic
import Capless.Renaming.Term.Subtyping
namespace Capless

theorem Typed.rename
  {Γ : Context n m k} {Δ : Context n' m k}
  (h : Typed Γ t E Ct)
  (ρ : VarMap Γ f Δ) :
  Typed Δ (t.rename f) (E.rename f) (Ct.rename f) := by
  induction h generalizing n'
  case var hb =>
    simp [Term.rename, EType.rename, CType.rename]
    apply Typed.var
    have hb1 := ρ.map _ _ hb
    simp [CType.rename] at hb1
    trivial
  case pack ih =>
    simp [Term.rename, EType.rename]
    apply Typed.pack
    have ih := ih (ρ.cext _)
    simp [Term.rename, EType.rename] at ih
    rw [<- CaptureSet.cweaken_rename_comm]
    exact ih
  case sub hsc hs ih =>
    apply Typed.sub
    apply ih; trivial
    apply! hsc.rename
    apply! hs.rename
  case abs iht =>
    simp [Term.rename, EType.rename, CType.rename, SType.rename]
    apply Typed.abs
    rw [CaptureSet.weaken_rename]
    apply? iht
    apply ρ.ext
  case tabs iht =>
    simp [Term.rename, EType.rename, CType.rename, SType.rename]
    apply Typed.tabs
    apply? iht
    apply ρ.text
  case cabs iht =>
    simp [Term.rename, EType.rename, CType.rename, SType.rename]
    apply Typed.cabs
    rw [<- CaptureSet.cweaken_rename_comm]
    apply? iht
    apply ρ.cext
  case app ih1 ih2 =>
    simp [Term.rename]
    simp [EType.rename_open]
    apply Typed.app
    have ih1 := ih1 ρ
    simp [Term.rename, EType.rename, CType.rename, SType.rename] at ih1
    exact ih1
    have ih2 := ih2 ρ
    simp [Term.rename, EType.rename] at ih2
    exact ih2
  case tapp ih =>
    simp [Term.rename]
    simp [EType.rename_topen]
    apply Typed.tapp
    have ih := ih ρ
    simp [Term.rename, EType.rename, CType.rename, SType.rename] at ih
    trivial
  case capp ih =>
    simp [Term.rename, EType.rename_copen]
    apply Typed.capp
    have ih := ih ρ
    simp [Term.rename, EType.rename, CType.rename, SType.rename] at ih
    trivial
  case box ih =>
    simp [Term.rename, EType.rename, CType.rename, SType.rename]
    apply Typed.box
    have ih := ih ρ
    simp [Term.rename, EType.rename] at ih
    trivial
  case unbox ih =>
    simp [Term.rename, EType.rename, CType.rename]
    apply Typed.unbox
    have ih := ih ρ
    simp [Term.rename, EType.rename, CType.rename, CaptureSet.rename_empty] at ih
    simp [SType.rename, CType.rename] at ih
    trivial
  case letin ih1 ih2 =>
    simp [Term.rename]
    apply Typed.letin
    have ih1 := ih1 ρ
    simp [EType.rename] at ih1
    exact ih1
    have ih2 := ih2 (ρ.ext _)
    rw [<- EType.weaken_rename] at ih2
    rw [CaptureSet.weaken_rename]
    trivial
  case letex ih1 ih2 =>
    simp [Term.rename]
    apply letex
    have ih1 := ih1 ρ
    simp [EType.rename] at ih1
    exact ih1
    have ih2 := ih2 ((ρ.cext _).ext _)
    rw [<- EType.cweaken_rename_comm]
    rw [EType.weaken_rename]
    rw [<- CaptureSet.cweaken_rename_comm]
    rw [CaptureSet.weaken_rename]
    trivial
  case bindt ih =>
    simp [Term.rename]
    apply Typed.bindt
    have ih := ih (ρ.text _)
    simp [Term.rename, TBinding.rename, EType.rename, CType.rename] at ih
    rw [EType.tweaken_rename] at ih
    trivial
  case bindc ih =>
    simp [Term.rename]
    apply Typed.bindc
    have ih := ih (ρ.cext _)
    simp [Term.rename, CBinding.rename] at ih
    rw [EType.cweaken_rename_comm] at ih
    rw [<- CaptureSet.cweaken_rename_comm]
    trivial

end Capless
