import Cappy.Translation.Encoding.Context
import Cappy.TypeSystem.Subcapturing
import Capless.Subcapturing
import Capless.Subcapturing.Basic
namespace Cappy

theorem subcapt_enc_monotonic
  (hg : Context.Interp Γ Δ)
  (h : Δ.ctx ⊢ D1 <:c D2)
  (hi1 : CaptureSet.Interp Δ.map Γ C D1 I1)
  (hi2 : CaptureSet.Interp Δ.map Γ C D2 I2) :
  (Δ.ctx ⊢ I1 <:c I2) := by
  induction C
  case empty =>
    cases hi1; cases hi2
    apply Capless.Subcapt.refl
  case union => sorry
  case singleton => sorry
  case reach => sorry
  case universal => sorry

end Cappy
