import Capless.Typing
import Capless.Subst.Basic
import Capless.Subst.Term.Subtyping
import Capless.Renaming.Term.Typing
namespace Capless

theorem Typed.subst
  {Γ : Context n m k} {Δ : Context n' m k}
  (h : Typed Γ t E Ct)
  (σ : VarSubst Γ f Δ) :
  Typed Δ (t.rename f) (E.rename f) (Ct.rename f) := by
  induction h generalizing n'
  case var hb =>
    simp [Term.rename, EType.rename, CType.rename]
    have hb1 := σ.map _ _ hb
    simp [CType.rename] at hb1
    apply Typed.precise_capture
    trivial
  case pack ih =>
    simp [Term.rename, EType.rename]
    apply pack
    have ih := ih σ.cext
    simp [EType.rename] at ih
    rw [<- CaptureSet.cweaken_rename_comm]
    exact ih
  case sub hsc hs ih =>
    apply sub
    { apply ih; trivial }
    { apply! hsc.subst }
    { apply! hs.subst }
  case abs hc ih =>
    simp [Term.rename, EType.rename, CType.rename, SType.rename]
    apply abs
    { rw [CaptureSet.weaken_rename]
      apply ih
      apply σ.ext }
  case tabs hc ih =>
    simp [Term.rename, EType.rename, CType.rename, SType.rename]
    apply tabs
    { apply ih
      apply σ.text }
  case cabs hc ih =>
    simp [Term.rename, EType.rename, CType.rename, SType.rename]
    apply cabs
    { rw [<- CaptureSet.cweaken_rename_comm]
      apply ih
      apply σ.cext }
  case app ih1 ih2 =>
    simp [Term.rename]
    rw [EType.rename_open]
    apply app
    { have ih1 := ih1 σ
      simp [Term.rename, EType.rename, CType.rename, SType.rename] at ih1
      exact ih1 }
    { have ih2 := ih2 σ
      simp [Term.rename, EType.rename, CType.rename, SType.rename] at ih2
      exact ih2 }
  case tapp ih =>
    simp [Term.rename]
    rw [EType.rename_topen]
    apply tapp
    have ih1 := ih σ
    simp [Term.rename, EType.rename, CType.rename, SType.rename] at ih1
    exact ih1
  case capp ih =>
    simp [Term.rename]
    rw [EType.rename_copen]
    apply capp
    have ih1 := ih σ
    simp [Term.rename, EType.rename, CType.rename, SType.rename] at ih1
    exact ih1
  case box ih =>
    simp [Term.rename, EType.rename, CType.rename, SType.rename]
    apply box
    have ih1 := ih σ
    simp [Term.rename, EType.rename, CType.rename, SType.rename] at ih1
    exact ih1
  case unbox ih =>
    simp [Term.rename, EType.rename, CType.rename, SType.rename]
    apply unbox
    have ih1 := ih σ
    simp [Term.rename, EType.rename, CType.rename, SType.rename] at ih1
    exact ih1
  case letin ih1 ih2 =>
    simp [Term.rename]
    apply letin
    { have ih1 := ih1 σ
      simp [EType.rename] at ih1
      exact ih1 }
    { have ih2 := ih2 (σ.ext _)
      rw [<- EType.weaken_rename] at ih2
      rw [CaptureSet.weaken_rename]
      exact ih2 }
  case letex ih1 ih2 =>
    simp [Term.rename]
    apply letex
    { have ih1 := ih1 σ
      simp [EType.rename] at ih1
      exact ih1 }
    { have ih2 := ih2 (σ.cext.ext _)
      rw [<- EType.weaken_rename] at ih2
      rw [EType.cweaken_rename_comm] at ih2
      rw [<- CaptureSet.cweaken_rename_comm]
      rw [CaptureSet.weaken_rename]
      exact ih2 }
  case bindt ih =>
    simp [Term.rename]
    apply bindt
    have ih := ih σ.text
    rw [EType.tweaken_rename] at ih
    simp [TBinding.rename] at ih
    exact ih
  case bindc ih =>
    simp [Term.rename]
    apply bindc
    have ih := ih σ.cext
    rw [EType.cweaken_rename_comm] at ih
    simp [CBinding.rename] at ih
    rw [<- CaptureSet.cweaken_rename_comm]
    exact ih

theorem Typed.open
  (h : Typed (Γ,x: P) t E Ct)
  (hx : Typed Γ (Term.var x) (EType.type P) Cx) :
  Typed Γ (t.open x) (E.open x) (Ct.open x) := by
  simp [Term.open, EType.open]
  apply Typed.subst
  { exact h }
  { apply VarSubst.open
    trivial }

end Capless
