import Capless.Subcapturing
namespace Capless

theorem Subcapt.refl :
  Subcapt Γ C C := by
  apply subset
  apply CaptureSet.subset_refl

end Capless
