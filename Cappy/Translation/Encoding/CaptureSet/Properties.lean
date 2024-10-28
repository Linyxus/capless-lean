import Cappy.Translation.Encoding.CaptureSet.Core
namespace Cappy

theorem CaptureSet.interp_inj
  (hi1 : CaptureSet.Interp ρ Γ C D I1)
  (hi2 : CaptureSet.Interp ρ Γ C D I2) :
  I1 = I2 := by
  induction hi1 generalizing I2 <;> try (solve | cases hi2; trivial)
  case i_union ih1 ih2 =>
    cases hi2
    aesop
  case i_singleton hb1 _ ih =>
    cases hi2; rename_i hb2 _
    have h := Context.bound_inj hb1 hb2
    aesop

end Cappy
