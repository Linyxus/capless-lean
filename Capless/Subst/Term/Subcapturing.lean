import Capless.Subst.Basic
import Capless.Subcapturing
import Capless.Typing.Basic
namespace Capless

theorem Subcapt.subst
  (h : Subcapt Γ C1 C2)
  (σ : VarSubst Γ f Δ) :
  Subcapt Δ (C1.rename f) (C2.rename f) := by
  induction h
  case trans => apply trans <;> aesop
  case subset hsub =>
    apply subset
    rename_i D1 D2 _
    cases D1; cases D2
    cases hsub; simp at *
    constructor <;> simp [CaptureSet.rename] <;>
      try (solve | apply Finset.image_subset_image; assumption | assumption)
  case union h1 h2 =>
    simp [CaptureSet.rename_union]
    apply union <;> aesop
  case var hb =>
    have ht := σ.map _ _ hb
    simp [EType.rename, CType.rename] at ht
    have h := Typing.inv_subcapt ht
    simp [CaptureSet.rename_singleton]; trivial
  case evar hb =>
    have ht := σ.map _ _ hb
    simp [EType.rename, CType.rename] at ht
    sorry

end Capless
