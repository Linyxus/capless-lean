import Capless.Store
import Capless.Subcapturing
import Capless.Subcapturing.Basic
import Capless.Inversion.Context

/-!
# Basic Properties of Well-Scopedness

This file contains basic properties of the well-scopedness relation.
-/

namespace Capless

theorem ReachSet.proj_empty {C : CaptureSet n k}
  (hr : ReachSet Γ (C.proj K) R)
  (he : K.IsEmpty)
  : R ⊆ .empty := by
  generalize h : C.proj K = D at hr
  induction hr generalizing C K
  case empty => constructor
  case union ha hb =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply CaptureSet.Subset.union_l (ha he (.refl _)) (hb he (.refl _))
  case var hb hr ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply ih _ (.refl _)
    apply Kind.Intersect.is_empty_r he
  case cinstr hb hr ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply ih _ (.refl _)
    apply Kind.Intersect.is_empty_r he
  case cbound hb hr ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply ih _ (.refl _)
    apply Kind.Intersect.is_empty_r he
  case ckind =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply CaptureSet.Subset.singleton_absurd
    apply Kind.Intersect.is_empty_r $ Kind.Intersect.is_empty_r he
  case label =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply CaptureSet.Subset.singleton_absurd
    apply Kind.Intersect.is_empty_r $ Kind.Intersect.is_empty_r he
  case absurd =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    constructor

theorem ReachSet.proj_absurd {C : CaptureSet n k}
  (he : K.IsEmpty)
  : ∃ R, R ⊆ .empty ∧ ReachSet Γ (C.proj K) R := by
  induction C
  case empty => exists .empty; apply And.intro .empty .empty
  case union ha hb =>
    have ⟨Ra, hsa, ha⟩ := ha
    have ⟨Rb, hbs, hb⟩ := hb
    exists Ra ∪ Rb
    apply And.intro
    apply! CaptureSet.Subset.union_l
    apply! union
  case singleton =>
    exists .empty
    apply And.intro .empty
    apply absurd
    apply Kind.Intersect.is_empty_r he

theorem ReachSet.inj
  (hr1 : ReachSet Γ C R1)
  (hr2 : ReachSet Γ C R2)
  : R1 ⊆ R2 := by
  induction hr1 generalizing R2
  case empty => apply CaptureSet.Subset.empty
  case union ha hb => cases hr2; apply! CaptureSet.Subset.union_monotone (ha _) (hb _)
  case var hb1 hr1 ih =>
    cases hr2
    case var hb2 hr2 => cases Context.bound_injective hb1 hb2; apply! ih
    case label hb2 => cases Context.bound_lbound_absurd hb1 hb2
    case absurd he => apply! hr1.proj_empty
  case cinstr hb1 hr1 ih =>
    cases hr2
    case cinstr hb2 hr2 => cases Context.cbound_injective hb1 hb2; apply! ih
    case cbound hb2 hr2 => cases Context.cbound_injective hb1 hb2
    case ckind hb2 => cases Context.cbound_injective hb1 hb2
    case absurd he => apply! hr1.proj_empty
  case cbound hb1 hr1 ih =>
    cases hr2
    case cinstr hb2 hr2 => cases Context.cbound_injective hb1 hb2
    case cbound hb2 hr2 => cases Context.cbound_injective hb1 hb2; apply! ih
    case ckind hb2 => cases Context.cbound_injective hb1 hb2
    case absurd he => apply! hr1.proj_empty
  case ckind hb1 =>
    cases hr2
    case cinstr hb2 hr2 => cases Context.cbound_injective hb1 hb2
    case cbound hb2 hr2 => cases Context.cbound_injective hb1 hb2
    case ckind hb2 => cases Context.cbound_injective hb1 hb2; constructor
    case absurd he => apply! CaptureSet.Subset.singleton_absurd (Kind.Intersect.is_empty_r _)
  case label hb1 =>
    cases hr2
    case var hb2 hr2 =>  cases Context.bound_lbound_absurd hb2 hb1
    case label hb2 => cases Context.lbound_inj hb1 hb2; subst_vars; constructor
    case absurd he => apply! CaptureSet.Subset.singleton_absurd (Kind.Intersect.is_empty_r _)
  case absurd => constructor


theorem ReachSet.subkind {C : CaptureSet n k}
  (hk : K.Subkind L)
  (hr : ReachSet Γ (C.proj L) R2)
  : ∃ R1, R1 ⊆ R2 ∧ ReachSet Γ (C.proj K) R1 := by
  generalize h : C.proj L = D at hr
  induction hr generalizing C L K
  case empty =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    exists .empty; apply And.intro .empty .empty
  case union ha hb =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    have ⟨Ra, hsa, ha⟩ := ha hk (.refl _)
    have ⟨Rb, hsb, hb⟩ := hb hk (.refl _)
    exists Ra ∪ Rb
    apply And.intro (.union_monotone hsa hsb)
    apply! union
  case var hb hr ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    have ⟨R, hs, h⟩ := ih (Kind.Intersect.with_subkind hk) (.refl _)
    exists R; apply And.intro hs (.var hb h)
  case cinstr hb hr ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    have ⟨R, hs, h⟩ := ih (Kind.Intersect.with_subkind hk) (.refl _)
    exists R; apply And.intro hs (.cinstr hb h)
  case cbound hb hr ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    have ⟨R, hs, h⟩ := ih (Kind.Intersect.with_subkind hk) (.refl _)
    exists R; apply And.intro hs (.cbound hb h)
  case ckind hb =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply Exists.intro
    apply And.intro _ (ckind hb)
    apply CaptureSet.Subset.singleton_subkind $ Kind.Intersect.with_subkind $ Kind.Intersect.with_subkind hk
  case label hb =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply Exists.intro
    apply And.intro _ (label hb)
    apply CaptureSet.Subset.singleton_subkind $ Kind.Intersect.with_subkind $ Kind.Intersect.with_subkind hk
  case absurd he =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    exists .empty; apply And.intro .empty
    apply absurd $ Kind.Subkind.empty_r_inv _ he
    apply Kind.Intersect.with_subkind hk


theorem ReachSet.singleton_subkind
  (hk : K.Subkind L)
  (hr : ReachSet Γ (.singleton s L) R2)
  : ∃ R1, R1 ⊆ R2 ∧ ReachSet Γ (.singleton s K) R1 := by
  rw [← Kind.Intersect.top_l (K:=L), ← CaptureSet.proj] at hr
  rw [← Kind.Intersect.top_l (K:=K), ← CaptureSet.proj]
  apply! subkind

theorem ReachSet.proj_merge' {C : CaptureSet n k}
  (hr1 : ReachSet Γ (C.proj L1) R1)
  (hr2 : ReachSet Γ (C.proj L2) R2)
  : ∃ R, R ⊆ (R1 ∪ R2) ∧ ReachSet Γ (C.proj (L1.union L2)) R := by
  generalize h : C.proj L1 = D at hr1
  induction hr1 generalizing C L1 L2 R2
  case empty =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    exists .empty; apply And.intro .empty .empty
  case union ha hb =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    cases hr2
    rename_i hr2a hr2b
    have ⟨Ra, hsa, ha⟩ := ha hr2a (.refl _)
    have ⟨Rb, hsb, hb⟩ := hb hr2b (.refl _)
    exists Ra ∪ Rb
    apply And.intro
    . apply CaptureSet.Subset.trans $ CaptureSet.Subset.union_monotone hsa hsb
      apply CaptureSet.Subset.union_l
      . apply CaptureSet.Subset.union_l (.union_rl $ .union_rl .rfl) (.union_rr $ .union_rl .rfl)
      . apply CaptureSet.Subset.union_l (.union_rl $ .union_rr .rfl) (.union_rr $ .union_rr .rfl)
    . apply! union
  case var C _ _ _ hb hr1 ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    cases hr2
    case var hb2 hr2 =>
      cases Context.bound_injective hb hb2
      have ⟨R', hs', h'⟩ := ih hr2 (.refl _)
      have ⟨R, hs, h⟩ := h'.subkind Kind.Intersect.union_r_subkind
      exists R
      apply And.intro (.trans hs hs') (.var hb h)
    case label hb2 => cases Context.bound_lbound_absurd hb hb2
    case absurd he =>
      have ⟨R2, hs2, hr2⟩ := proj_absurd (Γ:=Γ) (C:=C) he
      have ⟨R', hs', h'⟩ := ih hr2 (.refl _)
      have ⟨R, hs, h⟩ := h'.subkind Kind.Intersect.union_r_subkind
      exists R
      apply And.intro (.trans hs (.trans hs' (.union_monotone .rfl hs2))) (.var hb h)
  case cinstr C _ _ hb hr1 ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    cases hr2
    case cinstr hb2 hr2 =>
      cases Context.cbound_injective hb hb2
      have ⟨R', hs', h'⟩ := ih hr2 (.refl _)
      have ⟨R, hs, h⟩ := h'.subkind Kind.Intersect.union_r_subkind
      exists R
      apply And.intro (.trans hs hs') (.cinstr hb h)
    case cbound hb2 hr2 => cases Context.cbound_injective hb hb2
    case ckind hb2 => cases Context.cbound_injective hb hb2
    case absurd he =>
      have ⟨R2, hs2, hr2⟩ := proj_absurd (Γ:=Γ) (C:=C) he
      have ⟨R', hs', h'⟩ := ih hr2 (.refl _)
      have ⟨R, hs, h⟩ := h'.subkind Kind.Intersect.union_r_subkind
      exists R
      apply And.intro (.trans hs (.trans hs' (.union_monotone .rfl hs2))) (.cinstr hb h)
  case cbound C _ _ hb hr1 ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    cases hr2
    case cinstr hb2 hr2 => cases Context.cbound_injective hb hb2
    case cbound hb2 hr2 =>
      cases Context.cbound_injective hb hb2
      have ⟨R', hs', h'⟩ := ih hr2 (.refl _)
      have ⟨R, hs, h⟩ := h'.subkind Kind.Intersect.union_r_subkind
      exists R
      apply And.intro (.trans hs hs') (.cbound hb h)
    case ckind hb2 => cases Context.cbound_injective hb hb2
    case absurd he =>
      have ⟨R2, hs2, hr2⟩ := proj_absurd (Γ:=Γ) (C:=C) he
      have ⟨R', hs', h'⟩ := ih hr2 (.refl _)
      have ⟨R, hs, h⟩ := h'.subkind Kind.Intersect.union_r_subkind
      exists R
      apply And.intro (.trans hs (.trans hs' (.union_monotone .rfl hs2))) (.cbound hb h)
  case ckind c K _ hb =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    cases hr2
    case cinstr hb2 hr2 => cases Context.cbound_injective hb hb2
    case cbound hb2 hr2 => cases Context.cbound_injective hb hb2
    case ckind p _ hb2 =>
      cases Context.cbound_injective hb hb2
      exists {c=c| K.intersect (p.intersect (.union L1 L2))}
      apply And.intro
      . apply CaptureSet.Subset.trans (.singleton_subkind _) .proj_merge
        apply Kind.Subkind.trans (Kind.Intersect.with_subkind _) Kind.Intersect.union_r_subkind
        apply Kind.Intersect.union_r_subkind
      . apply! ckind
    case absurd he =>
      rename_i p
      exists {c=c| K.intersect (p.intersect (.union L1 L2))}
      apply And.intro
      . apply CaptureSet.Subset.union_rl (.singleton_subkind _)
        apply Kind.Intersect.with_subkind
        apply Kind.Subkind.trans Kind.Intersect.union_r_subkind (.union_l .rfl (.is_empty_l he))
      . apply! ckind

  case label x _ _ _ hb =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    cases hr2
    case var hb2 hr2 => cases Context.bound_lbound_absurd hb2 hb
    case label p c _ hb2 =>
      cases Context.lbound_inj hb hb2
      subst_vars
      exists {x=x| (Kind.classifier c).intersect (p.intersect (.union L1 L2))}
      apply And.intro
      . apply CaptureSet.Subset.trans (.singleton_subkind _) .proj_merge
        apply Kind.Subkind.trans (Kind.Intersect.with_subkind _) Kind.Intersect.union_r_subkind
        apply Kind.Intersect.union_r_subkind
      . apply! label
    case absurd he =>
      rename_i c _ _ p
      exists {x=x| (Kind.classifier c).intersect (p.intersect (.union L1 L2))}
      apply And.intro
      . apply CaptureSet.Subset.union_rl (.singleton_subkind _)
        apply Kind.Intersect.with_subkind
        apply Kind.Subkind.trans Kind.Intersect.union_r_subkind (.union_l .rfl (.is_empty_l he))
      . apply! label
  case absurd he =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    rename_i p
    have h0 : (p.intersect (L1.union L2)).Subkind (p.intersect L2) := by
      apply Kind.Subkind.trans Kind.Intersect.union_r_subkind
      apply Kind.Subkind.union_l (.is_empty_l he) .rfl
    have ⟨R, hs, h⟩ := hr2.singleton_subkind h0
    exists R
    apply And.intro (.union_rr hs)
    apply h

theorem ReachSet.proj_merge
  (hr1 : ReachSet Γ (.singleton s L1) R1)
  (hr2 : ReachSet Γ (.singleton s L2) R2)
  : ∃ R, R ⊆ (R1 ∪ R2) ∧ ReachSet Γ (.singleton s (L1.union L2)) R := by
  rw [← Kind.Intersect.top_l (K:=L1), ← CaptureSet.proj] at hr1
  rw [← Kind.Intersect.top_l (K:=L2), ← CaptureSet.proj] at hr2
  rw [← Kind.Intersect.top_l (K:=(L1.union L2)), ← CaptureSet.proj]
  apply! proj_merge'

theorem ReachSet.subset
  (hs : C1 ⊆ C2)
  (hr1 : ReachSet Γ C2 R2)
  : ∃ R1, R1 ⊆ R2 ∧ ReachSet Γ C1 R1 := by
  induction hs generalizing R2
  case empty =>
    exists .empty; apply And.intro .empty .empty
  case rfl =>
    exists R2; apply And.intro .rfl hr1
  case union_l ha hb =>
    have ⟨R1, hs1, h1⟩ := ha hr1
    have ⟨R2, hs2, h2⟩ := hb hr1
    exists R1 ∪ R2
    apply And.intro $ .union_l hs1 hs2
    apply! union
  case union_rl ih =>
    cases hr1
    rename_i R1 R2 h1 h2
    have ⟨R, hs, h⟩ := ih h1
    exists R; apply And.intro (.union_rl hs) h
  case union_rr ih =>
    cases hr1
    rename_i R1 R2 h1 h2
    have ⟨R, hs, h⟩ := ih h2
    exists R; apply And.intro (.union_rr hs) h
  case trans ha hb =>
    have ⟨Rb, hsb, hb⟩ := hb hr1
    have ⟨Ra, hsa, ha⟩ := ha hb
    exists Ra; apply! And.intro (.trans hsa hsb)
  case singleton_subkind hs => apply! singleton_subkind
  case singleton_absurd he => exists .empty; apply And.intro .empty (.absurd he)
  case proj_merge =>
    cases hr1
    apply! proj_merge


theorem ReachSet.capture_kind_absurd {Γ: Context n m k}
  (hk : CaptureKind Γ C K)
  (he : K.IsEmpty)
  : ∃ R, R ⊆ .empty ∧ ReachSet Γ C R := by
  induction hk
  case var hb hk ih =>
    have ⟨R, hs, h⟩ := ih he
    exists R; apply And.intro hs (var hb h)
  case label x c _ K hb =>
    exists {x=x|(Kind.classifier c).intersect K}
    apply And.intro (.singleton_absurd he)
    apply! label
  case cvar c K L hb =>
    exists {c=c|K.intersect L}
    apply And.intro (.singleton_absurd he)
    apply! ckind
  case cbound hb hk ih =>
    have ⟨R, hs, h⟩ := ih he
    exists R; apply And.intro hs
    apply! cbound
  case cinstr hb hk ih =>
    have ⟨R, hs, h⟩ := ih he
    exists R; apply And.intro hs
    apply! cinstr
  case sub hsk hk ih => apply ih (hsk.empty_r_inv he)
  case empty => exists .empty; apply And.intro .empty .empty
  case singleton_absurd he2 => exists .empty; apply! And.intro .empty (.absurd he2)
  case union ha hb =>
    have ⟨Ra, hsa, ha⟩ := ha he
    have ⟨Rb, hsb, hb⟩ := hb he
    exists Ra ∪ Rb
    apply And.intro (.union_l hsa hsb)
    apply! union

theorem ReachSet.subcapt
  (hr2 : ReachSet Γ C2 R2)
  (hs : Subcapt Γ C1 C2)
  : ∃ R1, R1 ⊆ R2 ∧ ReachSet Γ C1 R1 := by
  induction hs generalizing R2
  case trans ha hb =>
    have ⟨R2, hs2, hr⟩ := hb hr2
    have ⟨R1, hs1, hr⟩ := ha hr
    exists R1
    apply! And.intro (.trans hs1 hs2)
  case subset => apply! subset
  case union ha hb =>
    have ⟨Ra, hsa, hra⟩ := ha hr2
    have ⟨Rb, hsb, hrb⟩ := hb hr2
    exists Ra ∪ Rb
    apply And.intro (.union_l hsa hsb) (.union hra hrb)
  case var hb => exists R2; apply And.intro .rfl; apply! var
  case cinstl hb =>
    cases hr2
    case cinstr hb2 hr2 => cases Context.cbound_injective hb hb2; exists R2; apply! And.intro .rfl
    case cbound hb2 hr2 => cases Context.cbound_injective hb hb2
    case ckind hb2 => cases Context.cbound_injective hb hb2
    case absurd _ he => apply! proj_absurd
  case cinstr hb => exists R2; apply And.intro .rfl; apply! cinstr
  case cbound hb => exists R2; apply And.intro .rfl; apply! cbound
  case absurd hk he =>
    cases hr2
    apply capture_kind_absurd hk he

-- theorem WellScoped.subkind
--   (hsc : WellScoped Γ cont (.proj C K2))
--   (hs : K1.Subkind K2)
--   : WellScoped Γ cont (.proj C K1) := by
--   generalize h : C.proj K2 = D at hsc
--   induction hsc generalizing C K2 K1
--   case empty =>
--     unfold CaptureSet.proj at h; split at h <;> simp at h
--     simp; constructor
--   case union ha hb =>
--     unfold CaptureSet.proj at h; split at h <;> simp at h
--     have ⟨_, _⟩ := h; subst_vars; simp_all
--     apply! union (ha _ $ .refl _) (hb _ $ .refl _)
--   case singleton hb hsc ih =>
--     unfold CaptureSet.proj at h; split at h <;> simp at h
--     have ⟨_, _⟩ := h; subst_vars; simp_all
--     apply singleton hb
--     apply ih
--     apply Kind.Intersect.with_subkind hs
--     apply! refl
--   case csingleton hb hsc ih =>
--     unfold CaptureSet.proj at h; split at h <;> simp at h
--     have ⟨_, _⟩ := h; subst_vars; simp_all
--     apply csingleton hb
--     apply ih
--     apply Kind.Intersect.with_subkind hs
--     apply! refl
--   case cbound hb hsc ih =>
--     unfold CaptureSet.proj at h; split at h <;> simp at h
--     have ⟨_, _⟩ := h; subst_vars; simp_all
--     apply cbound hb
--     apply ih
--     apply Kind.Intersect.with_subkind hs
--     apply! refl
--   case ckind hb ih =>
--     unfold CaptureSet.proj at h; split at h <;> simp at h
--     have ⟨_, _⟩ := h; subst_vars; simp_all
--     apply! ckind
--   case label hb hl =>
--     unfold CaptureSet.proj at h; split at h <;> simp at h
--     have ⟨_, _⟩ := h; subst_vars; simp_all
--     apply! label
--   case label_disj hb hd =>
--     unfold CaptureSet.proj at h; split at h <;> simp at h
--     have ⟨_, _⟩ := h; subst_vars; simp_all
--     apply label_disj hb
--     apply hd.refine_subkind_l $ Kind.Intersect.with_subkind hs

-- theorem WellScoped.subkind_singleton
--   (hsc : WellScoped Γ cont (.singleton s L))
--   (hs : Kind.Subkind K L)
--   : WellScoped Γ cont (.singleton s K) := by
--   rw [← Kind.Intersect.top_l (K:=L)] at hsc
--   have h : CaptureSet.proj (.singleton s .top) L = .singleton s (.intersect .top L) := by simp
--   rw [← h] at hsc
--   have h1 := hsc.subkind hs
--   simp only [CaptureSet.proj] at h1
--   rw [Kind.Intersect.top_l] at h1
--   assumption

-- theorem WellScoped.subset {C1 C2 : CaptureSet n k}
--   (hsc : WellScoped Γ cont C2)
--   (hs : C1.Subset C2) : WellScoped Γ cont C1 := by
--   induction hs
--   case empty => apply empty
--   case rfl => assumption
--   case union_l ha hb iha ihb =>
--     apply! union (iha _) (ihb _)
--   case union_rl ha iha =>
--     cases hsc
--     apply! iha
--   case union_rr ha iha =>
--     cases hsc
--     apply! iha

-- theorem WellScoped.cons
--   (hsc : WellScoped Γ cont C) :
--   WellScoped Γ (Cont.cons u cont) C := by
--   induction hsc
--   case empty => apply empty
--   case union => apply union <;> aesop
--   case singleton ih => apply singleton <;> aesop
--   case csingleton ih => apply csingleton <;> aesop
--   case cbound ih => apply cbound <;> aesop
--   case ckind ih => apply ckind <;> aesop
--   case label hb hl =>
--     apply label hb
--     constructor; assumption
--   case label_disj hb hd =>
--     apply! label_disj

-- theorem WellScoped.conse
--   (hsc : WellScoped Γ cont C) :
--   WellScoped Γ (Cont.conse u cont) C := by
--   induction hsc
--   case empty => apply empty
--   case union => apply union <;> aesop
--   case singleton ih => apply singleton <;> aesop
--   case csingleton ih => apply csingleton <;> aesop
--   case cbound ih => apply cbound <;> aesop
--   case ckind ih => apply ckind <;> aesop
--   case label hb hl =>
--     apply label hb
--     constructor; assumption
--   case label_disj => apply! label_disj

-- theorem WellScoped.scope
--   (hsc : WellScoped Γ cont C) :
--   WellScoped Γ (Cont.scope x cont) C := by
--   induction hsc
--   case empty => apply empty
--   case union => apply union <;> aesop
--   case singleton ih => apply singleton <;> aesop
--   case csingleton ih => apply csingleton <;> aesop
--   case cbound ih => apply cbound <;> aesop
--   case ckind ih => apply ckind <;> aesop
--   case label hb hl =>
--     apply label hb
--     constructor; assumption
--   case label_disj => apply! label_disj


-- theorem WellScoped.proj_merge
--   (hsc1 : WellScoped Γ cont (.proj C K1))
--   (hsc2 : WellScoped Γ cont (.proj C K2))
--   : WellScoped Γ cont (.proj C (K1.union K2)) := by
--   generalize h : C.proj K1 = D at hsc1
--   induction hsc1 generalizing C K1 K2
--   case empty =>
--     unfold CaptureSet.proj at h; split at h <;> simp at h
--     simp; constructor
--   case union ha hb =>
--     unfold CaptureSet.proj at h; split at h <;> simp at h
--     have ⟨_, _⟩ := h; subst_vars; simp_all
--     cases hsc2
--     apply! union (ha _ $ .refl _) (hb _ $ .refl _)
--   case singleton hb hsc ih =>
--     unfold CaptureSet.proj at h; split at h <;> simp at h
--     have ⟨_, _⟩ := h; subst_vars; simp_all
--     cases hsc2
--     case singleton hb2 hsc2 =>
--       cases Context.bound_injective hb hb2
--       apply singleton hb
--       apply subkind _ Kind.Intersect.union_r_subkind
--       apply! ih _ (.refl _)
--     case label hb2 _ => cases Context.bound_lbound_absurd hb hb2
--     case label_disj hb2 _ => cases Context.bound_lbound_absurd hb hb2
--   case csingleton hb hsc ih =>
--     unfold CaptureSet.proj at h; split at h <;> simp at h
--     have ⟨_, _⟩ := h; subst_vars; simp_all
--     cases hsc2
--     case csingleton hb2 hsc2 =>
--       cases Context.cbound_injective hb hb2
--       apply csingleton hb
--       apply subkind _ Kind.Intersect.union_r_subkind
--       apply! ih _ (.refl _)
--     case cbound hb2 _ => cases Context.cbound_injective hb hb2
--     case ckind hb2 => cases Context.cbound_injective hb hb2
--   case cbound hb hsc ih =>
--     unfold CaptureSet.proj at h; split at h <;> simp at h
--     have ⟨_, _⟩ := h; subst_vars; simp_all
--     cases hsc2
--     case csingleton hb2 _ => cases Context.cbound_injective hb hb2
--     case cbound hb2 hsc2 =>
--       cases Context.cbound_injective hb hb2
--       apply cbound hb
--       apply subkind _ Kind.Intersect.union_r_subkind
--       apply! ih _ (.refl _)
--     case ckind hb2 => cases Context.cbound_injective hb hb2
--   case ckind hb =>
--     unfold CaptureSet.proj at h; split at h <;> simp at h
--     have ⟨_, _⟩ := h; subst_vars; simp_all
--     apply! ckind
--   case label hb hl =>
--     unfold CaptureSet.proj at h; split at h <;> simp at h
--     have ⟨_, _⟩ := h; subst_vars; simp_all
--     apply! label
--   case label_disj hb hd =>
--     unfold CaptureSet.proj at h; split at h <;> simp at h
--     have ⟨_, _⟩ := h; subst_vars; simp_all
--     cases hsc2
--     case singleton hb2 _ => cases Context.bound_lbound_absurd hb2 hb
--     case label hb hl => apply! label
--     case label_disj hb2 hd2 =>
--       cases Context.lbound_inj hb hb2
--       subst_vars
--       have h := Kind.Disjoint.union_l hd hd2
--       apply subkind_singleton (label_disj hb h) Kind.Intersect.union_r_subkind

-- theorem WellScoped.proj_merge_singleton
--   (hs1 : WellScoped Γ cont (.singleton s K1))
--   (hs2 : WellScoped Γ cont (.singleton s K2))
--   : WellScoped Γ cont (.singleton s (K1.union K2)) := by
--   rw [← Kind.Intersect.top_l (K:=K1)] at hs1
--   rw [← Kind.Intersect.top_l (K:=K2)] at hs2
--   rw [← CaptureSet.proj] at hs1 hs2
--   rw [← Kind.Intersect.top_l (K:=K1.union K2), ← CaptureSet.proj]
--   apply! proj_merge

-- theorem WellScoped.absurd
--   (hk : CaptureKind Γ C K)
--   (he : K.IsEmpty)
--   : WellScoped Γ cont C := by
--   induction hk
--   case var hb hk ih => apply! singleton hb (ih _)
--   case label hl =>
--     apply label_disj hl
--     apply Kind.Disjoint.symm
--     apply Kind.Disjoint.from_empty_intersect Kind.Intersect.lawful he
--   case cvar hb => apply ckind hb
--   case cbound hb hk ih => apply! cbound hb (ih _)
--   case cinstr hb hk ih => apply! csingleton hb (ih _)
--   case sub hs hk ih => apply ih; apply hs.empty_r_inv he
--   case empty => constructor
--   case absurd hk he1 ih => apply! ih
--   case union ha hb => simp_all; apply! union


-- theorem WellScoped.subcapt (hsc : WellScoped Γ cont C2) (hsub : Subcapt Γ C1 C2) : WellScoped Γ cont C1 := by
--   induction hsub
--   case trans ha hb iha ihb => apply! iha $ ihb _
--   case subset hsub => apply! hsc.subset
--   case union ha hb iha ihb =>
--     apply! union (iha _) (ihb _)
--   case var hb => apply! singleton
--   case cinstl hb =>
--     cases hsc
--     case csingleton hb1 _ =>
--       cases Context.cbound_injective hb1 hb
--       assumption
--     case cbound hb1 _ =>
--       cases Context.cbound_injective hb1 hb
--     case ckind hb1 =>
--       cases Context.cbound_injective hb1 hb
--   case cinstr hb => apply! csingleton
--   case cbound hb => apply! cbound
--   case subkind => apply! hsc.subkind_singleton
--   case absurd hk he => apply! absurd
--   case proj_split =>
--     cases hsc
--     apply! proj_merge_singleton

-- theorem WellScoped.var_inv
--   (hsc : WellScoped Γ cont {x=x|.top})
--   (hbx : Γ.Bound x (S^C)) :
--   WellScoped Γ cont C := by
--   cases hsc
--   case singleton hbx' _ =>
--     have h := Context.bound_injective hbx hbx'
--     cases h
--     rw [CaptureSet.proj_top] at *
--     trivial
--   case label =>
--     exfalso
--     apply Context.bound_lbound_absurd <;> easy
--   case label_disj =>
--     exfalso
--     apply Context.bound_lbound_absurd <;> easy

-- theorem WellScoped.label_inv
--   (hsc : WellScoped Γ cont {x=x|.top})
--   (hbl : Γ.LBound x c S) :
--   ∃ tail, cont.HasLabel x tail := by
--   cases hsc
--   case singleton =>
--     exfalso
--     apply Context.bound_lbound_absurd <;> easy
--   case label => aesop
--   case label_disj hd => cases hd.top_l.is_absurd

end Capless
