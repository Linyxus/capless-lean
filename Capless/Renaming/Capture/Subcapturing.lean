import Capless.Subcapturing
import Capless.Renaming.Basic
import Mathlib.Data.Finset.Image
namespace Capless

theorem Subcapt.crename
  (h : Subcapt Γ C1 C2)
  (ρ : CVarMap Γ f Δ) :
  Subcapt Δ (C1.crename f) (C2.crename f) := by
  induction h
  case trans ih1 ih2 => apply trans <;> aesop
  case subset hsub =>
    apply subset
    rename_i D1 D2 _
    cases D1; cases D2
    cases hsub; simp at *
    constructor <;> simp [CaptureSet.crename] <;>
      try (solve | apply Finset.image_subset_image; assumption | assumption)
  case union ih1 ih2 =>
    simp [CaptureSet.crename_union]
    apply union <;> aesop
  case var hb =>
    simp [CaptureSet.crename_singleton]
    apply var
    have hb1 := ρ.map _ _ hb
    simp [EType.crename, CType.crename] at hb1
    assumption
  -- case evar hbx =>
  --   simp [CaptureSet.crename_singleton]
  --   have hbx1 := ρ.map _ _ hbx
  --   simp [EType.crename, CType.crename] at hbx1
  --   rw [<- CaptureSet.cweaken_crename] at hbx1
  --   apply evar; trivial
  case cinstl hb =>
    simp [CaptureSet.crename_csingleton]
    have hb1 := ρ.cmap _ _ hb
    simp [CBinding.rename] at hb1
    apply cinstl
    assumption
  case cinstr hb =>
    simp [CaptureSet.crename_csingleton]
    have hb1 := ρ.cmap _ _ hb
    simp [CBinding.rename] at hb1
    apply cinstr
    assumption
  -- case reachl hb =>
  --   simp [CaptureSet.crename_csingleton, CaptureSet.crename_rsingleton]
  --   have hb1 := ρ.map _ _ hb
  --   simp [EType.crename] at hb1
  --   apply reachl; assumption
  -- case reachr hb =>
  --   simp [CaptureSet.crename_csingleton, CaptureSet.crename_rsingleton]
  --   have hb1 := ρ.map _ _ hb
  --   simp [EType.crename] at hb1
  --   apply reachr; assumption

end Capless
