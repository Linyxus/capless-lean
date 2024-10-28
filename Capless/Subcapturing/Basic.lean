import Capless.Subcapturing
namespace Capless

theorem Subcapt.refl :
  Subcapt Γ C C := by
  apply subset
  apply CaptureSet.subset_refl

theorem Subcapt.union_l
  (h : Subcapt Γ C C2) :
  Subcapt Γ C (C1 ∪ C2) := by
  apply Subcapt.trans
  { exact h }
  { apply Subcapt.subset
    aesop }

theorem Subcapt.union_r
  (h : Subcapt Γ C C1) :
  Subcapt Γ C (C1 ∪ C2) := by
  apply Subcapt.trans
  { exact h }
  { apply Subcapt.subset
    aesop }

theorem Subcapt.join
  (h1 : Subcapt Γ C1 D1)
  (h2 : Subcapt Γ C2 D2) :
  Subcapt Γ (C1 ∪ C2) (D1 ∪ D2) := by
  apply Subcapt.union
  { apply Subcapt.union_r; assumption }
  { apply Subcapt.union_l; assumption }

end Capless
