import Capless.Typing
import Capless.Subst.Basic
import Capless.Subst.Term.Subtyping
import Capless.Renaming.Term.Typing
namespace Capless

theorem Typed.subst
  {Γ : Context n m k} {Δ : Context n' m k}
  (h : Typed Γ t E)
  (σ : VarSubst Γ f Δ) :
  Typed Δ (t.rename f) (E.rename f) := by
  induction h generalizing n'
  case var hb =>
    simp [Term.rename, EType.rename]
    apply σ.map
    trivial
  case pack ih =>
    simp [Term.rename, EType.rename]
    apply pack
    have ih := ih σ
    simp [EType.rename] at ih
    rw [CType.copen_rename_comm] at ih
    exact ih
  case sub hs ih =>
    apply sub
    { apply ih; trivial }
    { apply hs.subst; trivial }
  case abs hc ih =>
    simp [Term.rename, EType.rename, CType.rename, SType.rename]
    apply abs
    { apply ih
      apply σ.ext }
    { have hc1 := hc.rename (f := f)
      simp [Term.rename] at hc1
      exact hc1 }
  case tabs hc ih =>
    simp [Term.rename, EType.rename, CType.rename, SType.rename]
    apply tabs
    { apply ih
      apply σ.text }
    { have hc1 := hc.rename (f := f)
      simp [Term.rename] at hc1
      exact hc1 }
  case cabs hc ih =>
    simp [Term.rename, EType.rename, CType.rename, SType.rename]
    apply cabs
    { apply ih
      apply σ.cext }
    { have hc1 := hc.rename (f := f)
      simp [Term.rename] at hc1
      exact hc1 }
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
    exact ih

theorem Typed.open
  (h : Typed (Γ.var P) t E)
  (hx : Typed Γ (Term.var x) (EType.type P)) :
  Typed Γ (t.open x) (E.open x) := by
  simp [Term.open, EType.open]
  apply Typed.subst
  { exact h }
  { apply VarSubst.open
    trivial }

theorem Typed.narrow
  (h : Typed (Γ.var T) t E)
  (hs : CSubtyp Γ T' T) :
  Typed (Γ.var T') t E := by
  rw [<- EType.rename_id (E := E)]
  rw [<- Term.rename_id (t := t)]
  apply Typed.subst
  { exact h }
  { apply VarSubst.narrow
    trivial }

end Capless
