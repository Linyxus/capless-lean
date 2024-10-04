import Capless.Subcapturing
namespace Capless

theorem Subcapt.refl :
  Subcapt Γ C C := by
  apply subset
  apply CaptureSet.subset_refl

theorem Subcapt.join
  (h1 : Γ ⊢ C1 <:c D1)
  (h2 : Γ ⊢ C2 <:c D2) :
  Γ ⊢ C1 ∪ C2 <:c D1 ∪ D2 := by
  apply Subcapt.union
  { apply Subcapt.trans; exact h1
    apply Subcapt.subset; apply CaptureSet.Subset.union_rl; apply CaptureSet.subset_refl }
  { apply Subcapt.trans; exact h2
    apply Subcapt.subset; apply CaptureSet.Subset.union_rr; apply CaptureSet.subset_refl }

end Capless
