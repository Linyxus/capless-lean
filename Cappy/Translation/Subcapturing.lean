import Cappy.Translation.Encoding.Context
import Cappy.TypeSystem.Subcapturing
import Capless.Subcapturing
import Capless.Subcapturing.Basic
namespace Cappy

theorem CaptureSet.interp_monotonic_subcapt
  (h : Δ ⊢ D1 <:c D2)
  (hi1 : CaptureSet.Interp ρ Γ C D1 I1)
  (hi2 : CaptureSet.Interp ρ Γ C D2 I2) :
  (Δ ⊢ I1 <:c I2) := by
  induction C generalizing I1 I2
  case empty =>
    cases hi1; cases hi2
    apply Capless.Subcapt.refl
  case union C1 C2 ih1 ih2 =>
    cases hi1; cases hi2
    apply Capless.Subcapt.join
    { aesop }
    { aesop }
  case singleton =>
    cases hi1; cases hi2
    rename_i hb1 hi1 _ _ hb2 hi2
    have h := Context.bound_inj hb1 hb2
    cases h
    have h := CaptureSet.interp_inj hi1 hi2
    cases h
    apply Capless.Subcapt.refl
  case reach =>
    cases hi1; cases hi2
    apply Capless.Subcapt.refl
  case universal =>
    cases hi1; cases hi2
    assumption

theorem CaptureSet.interp_monotonic_subset
  (hi1 : CaptureSet.Interp ρ Γ C1 D I1)
  (hi2 : CaptureSet.Interp ρ Γ C2 D I2)
  (hsub : C1 ⊆ C2) :
  I1 ⊆ I2 := by
  induction hsub generalizing I1 I2
  case empty => cases hi1; aesop
  case rfl =>
    have h := CaptureSet.interp_inj hi1 hi2
    aesop
  case union_l =>
    cases hi1
    aesop
  case union_rl => cases hi2; aesop
  case union_rr => cases hi2; aesop

theorem CaptureSet.interp_meet
  (h1 : CaptureSet.Interp ρ Γ C D1 I1)
  (h2 : CaptureSet.Interp ρ Γ C D2 I2) :
  ∃ D3 I3,
    CaptureSet.Interp ρ Γ C D3 I3 ∧
    (Δ ⊢ I1 <:c I3) ∧ (Δ ⊢ I2 <:c I3) := by
  have ⟨I3, h3⟩ := CaptureSet.interp_complete (ρ := ρ) (Γ := Γ) (C := C) (D := D1 ∪ D2)
  apply Exists.intro (D1 ∪ D2)
  apply Exists.intro I3
  constructor; assumption
  constructor
  { apply CaptureSet.interp_monotonic_subcapt (hi1 := h1) (hi2 := h3)
    apply Capless.Subcapt.subset; aesop }
  { apply CaptureSet.interp_monotonic_subcapt (hi1 := h2) (hi2 := h3)
    apply Capless.Subcapt.subset; aesop }

theorem CaptureSet.interp_monotonic_alt
  (hsc : Subcapt Γ C1 C2)
  (hi1 : CaptureSet.Interp ρ Γ C1 D1 I1) :
  ∃ D2 I2, CaptureSet.Interp ρ Γ C2 D2 I2 ∧ Δ ⊢ I1 <:c I2 := by
  induction hsc generalizing D1 I1
  case sc_trans ih1 ih2 =>
    have ⟨D2, I2, hi2, hsc2⟩ := ih1 hi1
    have ⟨D3, I3, hi3, hsc3⟩ := ih2 hi2
    have hsc0 := Capless.Subcapt.trans hsc2 hsc3
    aesop
  case sc_var hb1 =>
    cases hi1; rename_i hb2 hi1
    have h := Context.bound_inj hb1 hb2
    cases h
    have hsc0 := Capless.Subcapt.refl (Γ := Δ) (C := I1)
    aesop
  case sc_elem C1 C2 hs =>
    have ⟨I2, hi2⟩ := CaptureSet.interp_complete (ρ:=ρ) (Γ:=Γ) (C:=C2) (D:=D1)
    have h := CaptureSet.interp_monotonic_subset hi1 hi2 hs
    have h := Capless.Subcapt.subset (Γ:=Δ) h
    aesop
  case sc_set C1 C2 C _ _ ih1 ih2 =>
    cases hi1; rename_i I11 I12 hi11 hi12
    have ⟨D21, I21, h21, hs21⟩ := ih1 hi11
    have ⟨D22, I22, h22, hs22⟩ := ih2 hi12
    have ⟨D3, I3, hi3, hs1, hs2⟩ := CaptureSet.interp_meet (Δ:=Δ) h21 h22
    apply Exists.intro D3; apply Exists.intro I3
    constructor; assumption
    apply Capless.Subcapt.union <;> (apply Capless.Subcapt.trans <;> assumption)

end Cappy
