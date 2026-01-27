import Capless.Subcapturing
import Capless.Subst.Basic
import Capless.WellScoped.Basic

/-
Substitution theorems for capture variable substitution in subcapturing judgments.
-/

namespace Capless

private theorem ReachSet.of_capture_kind
  (hr : ReachSet Γ C R)
  (hk : CaptureKind Γ C K)
  : R ⊆ R.proj K := by
  induction hr
  case empty => apply CaptureSet.Subset.empty
  case union ha hb =>
    have ⟨_, _⟩ := hk.union_l_inv
    apply! CaptureSet.Subset.union_monotone (ha _) (hb _)
  case var hb hr ih =>
    cases hk.var_lookup_inv hb <;> rename_i hk
    . apply! ih
    . apply ih (.absurd hk)
  case cinstr hb hr ih =>
    cases hk.cinst_lookup_inv hb <;> rename_i hk
    . apply! ih
    . apply ih (.absurd hk)
  case cbound hb hr ih =>
    cases hk.cbound_lookup_inv hb <;> rename_i hk
    . apply! ih
    . apply ih (.absurd hk)
  case ckind hb =>
    cases hk.ckind_lookup_inv hb
    . apply! CaptureSet.Subset.singleton_subkind (.of_intersect .rfl _)
    . apply CaptureSet.Subset.trans (.singleton_absurd _) .empty
      apply! Kind.intersect.is_empty_r
  case label hb =>
    cases hk.label_lookup_inv hb
    . apply! CaptureSet.Subset.singleton_subkind (.of_intersect .rfl _)
    . apply CaptureSet.Subset.trans (.singleton_absurd _) .empty
      apply! Kind.intersect.is_empty_r
  case var_reach ih => apply ih hk.with_reach_inv
  case cvar_creach ih => apply ih hk.with_reach_inv
  case absurd => exact .empty


private theorem drop_repeat_intersect_right : Kind.Subkind (.intersect L K) (Kind.intersect K (L.intersect K)) := by
  rw [Kind.Subkind.semantics]
  intro c ha
  have h1 := Kind.Intersect.lawful L K
  have h2 := Kind.Intersect.lawful K (L.intersect K)
  have ⟨_, _⟩ := h1.contains_inv ha
  apply! h2.contains

private theorem ReachSet.from_capture_kind
  (hk : CaptureKind Γ C K)
  : ∃ R, (Subcapt Γ R ((C.proj K).with_reach)) ∧ ReachSet Γ C R := by
  induction hk
  case var hb hk ih =>
    have ⟨R, h, ih⟩ := ih
    exists R
    apply And.intro _ (var hb ih)
    apply Subcapt.trans (.subset $ ih.of_capture_kind hk)
    rw [← CaptureSet.reach_proj]
    apply Subcapt.apply_proj
    apply Subcapt.reachsetl (var hb ih)
  case label hb =>
    apply Exists.intro
    apply And.intro _ (.label hb)
    apply Subcapt.subset (.trans .var_reach (.singleton_subkind drop_repeat_intersect_right))
  case cvar hb =>
    apply Exists.intro
    apply And.intro _ (.ckind hb)
    rw [← CaptureSet.reach_proj]
    apply Subcapt.subset (.singleton_subkind drop_repeat_intersect_right)
  case cbound hb hk ih =>
    have ⟨R, h, ih⟩ := ih
    exists R
    apply And.intro _ (cbound hb ih)
    apply Subcapt.trans (.subset $ ih.of_capture_kind hk)
    rw [← CaptureSet.reach_proj]
    apply Subcapt.apply_proj
    apply Subcapt.reachsetl (cbound hb ih)
  case cinstr hb hk ih =>
    have ⟨R, h, ih⟩ := ih
    exists R
    apply And.intro _ (cinstr hb ih)
    apply Subcapt.trans (.subset $ ih.of_capture_kind hk)
    rw [← CaptureSet.reach_proj]
    apply Subcapt.apply_proj
    apply Subcapt.reachsetl (cinstr hb ih)
  case sub ih =>
    have ⟨R, h, ih⟩ := ih
    exists R
    apply And.intro _ ih
    apply Subcapt.trans h
    simp [← CaptureSet.reach_proj]
    apply! Subcapt.subkind
  case empty => exists ∅; apply And.intro (.subset .empty) .empty
  case singleton_absurd he =>
    exists .empty; apply And.intro (.subset .empty) (.absurd he)
  case union ha hb =>
    have ⟨Ra, ha, iha⟩ := ha
    have ⟨Rb, hb, ihb⟩ := hb
    exists Ra ∪ Rb
    apply And.intro (.join ha hb) (.union iha ihb)
  case reach ih =>
    have ⟨R, h, ih⟩ := ih
    exists R
    apply And.intro _ ih.with_reach
    rw [CaptureSet.reach_proj, CaptureSet.reach_reach]
    apply h

theorem ReachSet.csubst
  {Γ : Context n m k} {Δ : Context n m k'}
  (h : ReachSet Γ C R)
  (σ : CVarSubst Γ f Δ) :
  ∃ R', (Δ ⊢ R' <:c (R.crename f)) ∧ ReachSet Δ (C.crename f) R' := by
  induction h generalizing k'
  case empty => exists .empty; apply And.intro (.subset .empty) .empty
  case union ih1 ih2 =>
    have ⟨R1, hs1, h1⟩ := ih1 σ
    have ⟨R2, hs2, h2⟩ := ih2 σ
    exists R1 ∪ R2
    simp
    apply And.intro $ .join hs1 hs2
    apply! union
  case var hb hr ih =>
    have hb1 := σ.map _ _ hb
    simp [CType.crename] at hb1
    have ⟨R, hs, h⟩ := ih σ
    exists R
    apply And.intro hs
    apply var hb1
    rw [← CaptureSet.proj_crename]; exact h
  case cinstr hb hr ih =>
    have hb1 := σ.cmap _ _ hb
    simp [CBinding.crename] at hb1
    have ⟨R, hs, h⟩ := ih σ
    exists R
    apply And.intro hs
    apply cinstr hb1
    rw [← CaptureSet.proj_crename]; exact h
  case cbound L _ hb hr ih =>
    have hb1 := σ.cmap_bound _ _ hb
    cases hb1; rename_i hb1
    have ⟨R1, hs1, h1⟩ := ih σ
    have hb1' := hb1.apply_proj (K:=L)
    rw [CaptureSet.proj, Kind.intersect.top_l, ← CaptureSet.proj_crename] at hb1'
    have ⟨R2, hs2, h2⟩ := h1.subcapt hb1'
    exists R2
    apply And.intro $ .trans (.subset hs2) hs1
    exact h2
  case ckind c K L hb =>
    have hb1 := σ.cmap_bound _ _ hb
    cases hb1; rename_i hb1
    have hb1 := hb1.apply_proj_singleton' (L:=L)
    have ⟨R, h, ih⟩ := ReachSet.from_capture_kind $ hb1.sub Kind.Intersect.subkind_r
    exists R
    apply And.intro _ ih
    rw [← CaptureSet.reach_proj, CaptureSet.with_reach, Singleton.with_reach, CaptureSet.proj] at h
    apply Subcapt.trans h (.subset $ .singleton_subkind Kind.Intersect.subkind_symm)
  case label c S L hb =>
    have hb1 := σ.lmap _ _ _ hb
    rename_i x
    exists {x=x|((Kind.classifier c).intersect L)}
    apply And.intro
    . apply Subcapt.subset CaptureSet.Subset.rfl
    . apply label hb1
  case absurd he =>
    exists ∅; apply And.intro; apply Subcapt.subset CaptureSet.Subset.empty; apply! absurd
  case var_reach ih =>
    have ⟨R, h, ih⟩ := ih σ
    apply Exists.intro
    apply And.intro h ih.var_reach
  case cvar_creach ih =>
    have ⟨R, h, ih⟩ := ih σ
    apply Exists.intro
    apply And.intro h ih.cvar_creach

theorem CaptureKind.csubst
  (h : CaptureKind Γ C K)
  (σ : CVarSubst Γ f Δ) :
  CaptureKind Δ (C.crename f) K := by
  induction h
  case var hb hk ih =>
    rewrite [CaptureSet.proj_crename] at ih
    apply! var (σ.map _ _ hb) (ih _)
  case label hb => apply label (σ.lmap _ _ _ hb)
  case cvar hb =>
    cases σ.cmap_bound _ _ hb
    case set_kind hsk1 =>
      apply hsk1.apply_proj_singleton
  case cbound hb hk ih =>
    rewrite [CaptureSet.proj_crename] at ih
    cases σ.cmap_bound _ _ hb
    rename_i hb
    apply subcapt _ hb.apply_proj_singleton
    apply! ih
  case cinstr hb hk ih =>
    rewrite [CaptureSet.proj_crename] at ih
    apply! cinstr (σ.cmap _ _ hb) (ih _)
  case sub hs hk ih =>
    apply! sub hs (ih _)
  case empty => apply empty
  case singleton_absurd => apply! singleton_absurd
  case union ha hb => apply! union (ha _) (hb _)
  case reach ih =>
    rw [CaptureSet.reach_crename]
    apply! reach $ ih _

theorem Subcapt.csubst
  (h : Subcapt Γ C1 C2)
  (σ : CVarSubst Γ f Δ) :
  Subcapt Δ (C1.crename f) (C2.crename f) := by
  induction h <;> try rw [CaptureSet.proj_crename]
  case trans ha hb => apply! trans (ha _) (hb _)
  case subset hs => apply subset (CaptureSet.Subset.crename hs)
  case union ha hb => apply! union (ha _) (hb _)
  case var hb => apply var (σ.map _ _ hb)
  case cinstl hb => apply cinstl (σ.cmap _ _ hb)
  case cinstr hb => apply cinstr (σ.cmap _ _ hb)
  case cbound hb =>
    cases σ.cmap_bound _ _ hb
    apply! apply_proj_singleton
  case proj_r hk => apply! proj_r (hk.csubst _)
  case reachsetl hr =>
    rw [CaptureSet.reach_crename]
    have ⟨R, h, hr⟩ := hr.csubst σ



end Capless
