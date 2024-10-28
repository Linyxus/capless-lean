import Cappy.Translation.Encoding.Context
import Cappy.TypeSystem.Subcapturing
import Capless.Subcapturing
import Capless.Subcapturing.Basic
namespace Cappy

theorem subcapt_enc_monotonic
  (hg : Context.Interp Γ ⟨Δ, ρ⟩)
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

end Cappy
