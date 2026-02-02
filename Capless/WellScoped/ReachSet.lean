import Capless.Store
import Capless.Inversion.Context

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
    apply Kind.intersect.is_empty_r he
  case cinstr hb hr ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply ih _ (.refl _)
    apply Kind.intersect.is_empty_r he
  case cbound hb hr ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply ih _ (.refl _)
    apply Kind.intersect.is_empty_r he
  case ckind =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply CaptureSet.Subset.singleton_absurd
    apply Kind.intersect.is_empty_r $ Kind.intersect.is_empty_r he
  case label =>
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    have ⟨_, _⟩ := h; subst_vars; simp_all [-Kind.intersect]
    apply CaptureSet.Subset.singleton_absurd
    apply Kind.intersect.is_empty_r $ Kind.intersect.is_empty_r he
  case var_reach hr ih =>
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    case h_3 =>
      have ⟨h1, h2⟩ := h
      cases h1; subst h2
      rename_i x _ _ p
      apply ih (C := {x=x|p}) (K := K) he (.refl _)
  case cvar_creach hr ih =>
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    case h_3 =>
      have ⟨h1, h2⟩ := h
      cases h1; subst h2
      rename_i c _ _ p
      apply ih (C := {c=c|p}) (K := K) he (.refl _)
  case absurd =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    constructor

theorem ReachSet.singleton_proj_empty
  (hr : ReachSet Γ (.singleton s K) R)
  (he : K.IsEmpty)
  : R ⊆ ∅ := by
  rw [← Kind.intersect.top_l (K:=K), ← CaptureSet.proj] at hr
  apply proj_empty hr he


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
    apply Kind.intersect.is_empty_r he

theorem ReachSet.inj
  (hr1 : ReachSet Γ C R1)
  (hr2 : ReachSet Γ C R2)
  : R1 ⊆ R2 := by
  induction hr1 generalizing R2
  case empty => apply CaptureSet.Subset.empty
  case union ha hb =>
    cases hr2
    case union => apply! CaptureSet.Subset.union_monotone (ha _) (hb _)
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
    case absurd he => apply! CaptureSet.Subset.singleton_absurd (Kind.intersect.is_empty_r _)
  case label hb1 =>
    cases hr2
    case var hb2 hr2 =>  cases Context.bound_lbound_absurd hb2 hb1
    case label hb2 => cases Context.lbound_inj hb1 hb2; subst_vars; constructor
    case absurd he => apply! CaptureSet.Subset.singleton_absurd (Kind.intersect.is_empty_r _)
  case var_reach hr1 ih =>
    cases hr2
    case var_reach => apply! ih
    case absurd he => apply! hr1.singleton_proj_empty
  case cvar_creach ih =>
    cases hr2
    case cvar_creach => apply! ih
    case absurd he => apply! singleton_proj_empty
  case absurd => constructor

private theorem drop_repeat_intersect_left : Kind.Subkind (K.intersect L) (Kind.intersect K (K.intersect L)) := by
  rw [← Kind.intersect.assoc]
  apply Kind.Intersect.with_subkind_r
  apply Kind.Intersect.subkind_self

theorem ReachSet.idempotent
  (hr : ReachSet Γ C R) :
  ∃ R', R' ⊆ R ∧ R ⊆ R' ∧ ReachSet Γ R R' := by
  induction hr <;> try assumption
  case empty => apply Exists.intro; apply And.intro .empty (.intro .empty .empty)
  case union ha hb =>
    have ⟨R1, h1, h1', hr1⟩ := ha
    have ⟨R2, h2, h2', hr2⟩ := hb
    exists R1 ∪ R2
    apply And.intro (.union_monotone h1 h2) (.intro (.union_monotone h1' h2') (.union hr1 hr2))
  case ckind hb =>
    apply Exists.intro
    apply And.intro (.singleton_subkind Kind.Intersect.subkind_r) (.intro (.singleton_subkind drop_repeat_intersect_left) (cvar_creach $ ckind hb))
  case label hb =>
    apply Exists.intro
    apply And.intro (.singleton_subkind Kind.Intersect.subkind_r) (.intro (.singleton_subkind drop_repeat_intersect_left) (label hb))
  case absurd => apply Exists.intro; apply And.intro .empty (.intro .empty .empty)

theorem ReachSet.subkind {C : CaptureSet n k}
  (hr : ReachSet Γ (C.proj L) R2)
  (hk : K.Subkind L)
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
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    have ⟨_, _⟩ := h; subst_vars; simp_all [-Kind.intersect]
    apply Exists.intro
    apply And.intro _ (label hb)
    apply CaptureSet.Subset.singleton_subkind $ Kind.Intersect.with_subkind $ Kind.Intersect.with_subkind hk
  case absurd he =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    exists .empty; apply And.intro .empty
    apply absurd $ Kind.Subkind.empty_r_inv _ he
    apply Kind.Intersect.with_subkind hk
  case var_reach hr ih =>
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    have ⟨_, _⟩ := h; subst_vars
    rename_i x _ _ p
    have ⟨R1, hs1, hr1⟩ := ih (C:={x=x|p}) hk (.refl _)
    exists R1
    apply And.intro hs1 hr1.var_reach
  case cvar_creach hr ih =>
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    have ⟨_, _⟩ := h; subst_vars
    rename_i c _ _ p
    have ⟨R1, hs1, hr1⟩ := ih (C:={c=c|p}) hk (.refl _)
    exists R1
    apply And.intro hs1 hr1.cvar_creach



theorem ReachSet.singleton_subkind
  (hr : ReachSet Γ (.singleton s L) R2)
  (hk : K.Subkind L)
  : ∃ R1, R1 ⊆ R2 ∧ ReachSet Γ (.singleton s K) R1 := by
  rw [← Kind.intersect.top_l (K:=L), ← CaptureSet.proj] at hr
  rw [← Kind.intersect.top_l (K:=K), ← CaptureSet.proj]
  apply! subkind

theorem ReachSet.proj_merge' {C : CaptureSet n k}
  (hr1 : ReachSet Γ (C.proj L1) R1)
  (hr2 : ReachSet Γ (C.proj L2) R2)
  : ∃ R, R ⊆ (R1 ∪ R2) ∧ ReachSet Γ (C.proj (L1 ++ L2)) R := by
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
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    have ⟨_, _⟩ := h; subst_vars; simp_all [-Kind.intersect]
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
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    have ⟨_, _⟩ := h; subst_vars; simp_all [-Kind.intersect]
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
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    have ⟨_, _⟩ := h; subst_vars; simp_all [-Kind.intersect]
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
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    have ⟨_, _⟩ := h; subst_vars; simp_all [-Kind.intersect]
    cases hr2
    case cinstr hb2 hr2 => cases Context.cbound_injective hb hb2
    case cbound hb2 hr2 => cases Context.cbound_injective hb hb2
    case ckind p _ hb2 =>
      cases Context.cbound_injective hb hb2
      exists .singleton (.creach c) (K.intersect (p.intersect (L1 ++ L2)))
      apply And.intro
      . apply CaptureSet.Subset.trans (.singleton_subkind _) .proj_merge
        apply Kind.Subkind.trans (Kind.Intersect.with_subkind _) Kind.Intersect.union_r_subkind
        apply Kind.Intersect.union_r_subkind
      . apply! ckind
    case absurd he =>
      rename_i p
      exists .singleton (.creach c) (K.intersect (p.intersect (L1 ++ L2)))
      apply And.intro
      . apply CaptureSet.Subset.union_rl (.singleton_subkind _)
        apply Kind.Intersect.with_subkind
        apply Kind.Subkind.trans Kind.Intersect.union_r_subkind (.union_l .rfl (.is_empty_l he))
      . apply! ckind

  case label x _ _ _ hb =>
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    have ⟨_, _⟩ := h; subst_vars; simp_all [-Kind.intersect]
    cases hr2
    case var hb2 hr2 => cases Context.bound_lbound_absurd hb2 hb
    case label p c _ hb2 =>
      cases Context.lbound_inj hb hb2
      subst_vars
      exists {x=x| (Kind.classifier c).intersect (p.intersect (L1 ++ L2))}
      apply And.intro
      . apply CaptureSet.Subset.trans (.singleton_subkind _) .proj_merge
        apply Kind.Subkind.trans (Kind.Intersect.with_subkind _) Kind.Intersect.union_r_subkind
        apply Kind.Intersect.union_r_subkind
      . apply! label
    case absurd he =>
      rename_i c _ _ p
      exists {x=x| (Kind.classifier c).intersect (p.intersect (L1 ++ L2))}
      apply And.intro
      . apply CaptureSet.Subset.union_rl (.singleton_subkind _)
        apply Kind.Intersect.with_subkind
        apply Kind.Subkind.trans Kind.Intersect.union_r_subkind (.union_l .rfl (.is_empty_l he))
      . apply! label
  case absurd he =>
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    have ⟨_, _⟩ := h; subst_vars; simp_all [-Kind.intersect]
    rename_i p
    have h0 : (p.intersect (L1 ++ L2)).Subkind (p.intersect L2) := by
      apply Kind.Subkind.trans Kind.Intersect.union_r_subkind
      apply Kind.Subkind.union_l (.is_empty_l he) .rfl
    have ⟨R, hs, h⟩ := hr2.singleton_subkind h0
    exists R
    apply And.intro (.union_rr hs)
    apply h
  case var_reach hr1 ih =>
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    have ⟨_, _⟩ := h; subst_vars; simp_all [-Kind.intersect]
    cases hr2
    case var_reach hr2 =>
      rename_i x _ _ p
      have ⟨R0, hs0, hr0⟩ := ih (C:={x=x|p}) hr2 (.refl _)
      exists R0
      apply And.intro hs0 hr0.var_reach
    case absurd he =>
      rename_i x _ _ p
      have ⟨R0, hs0, hr0⟩ := ih (C:={x=x|p}) (absurd he) (.refl _)
      exists R0
      apply And.intro hs0 hr0.var_reach
  case cvar_creach hr1 ih =>
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    have ⟨_, _⟩ := h; subst_vars; simp_all [-Kind.intersect]
    cases hr2
    case cvar_creach hr2 =>
      rename_i c _ _ p
      have ⟨R0, hs0, hr0⟩ := ih (C:={c=c|p}) hr2 (.refl _)
      exists R0
      apply And.intro hs0 hr0.cvar_creach
    case absurd he =>
      rename_i c _ _ p
      have ⟨R0, hs0, hr0⟩ := ih (C:={c=c|p}) (absurd he) (.refl _)
      exists R0
      apply And.intro hs0 hr0.cvar_creach

theorem ReachSet.proj_merge
  (hr1 : ReachSet Γ (.singleton s L1) R1)
  (hr2 : ReachSet Γ (.singleton s L2) R2)
  : ∃ R, R ⊆ (R1 ∪ R2) ∧ ReachSet Γ (.singleton s (L1 ++ L2)) R := by
  rw [← Kind.intersect.top_l (K:=L1), ← CaptureSet.proj] at hr1
  rw [← Kind.intersect.top_l (K:=L2), ← CaptureSet.proj] at hr2
  rw [← Kind.intersect.top_l (K:=(L1 ++ L2)), ← CaptureSet.proj]
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
  case var_reach =>
    cases hr1
    case var_reach => exists R2; apply! And.intro .rfl
    case absurd he =>
      exists .empty; apply And.intro .empty (.absurd he)
  case cvar_creach =>
    cases hr1
    case cvar_creach => exists R2; apply! And.intro .rfl
    case absurd he =>
      exists .empty; apply And.intro .empty (.absurd he)
  case proj_merge =>
    cases hr1
    apply! proj_merge

theorem ReachSet.with_reach
  (hr : ReachSet Γ C R)
  : ReachSet Γ C.with_reach R := by
  induction hr
  case empty => apply empty
  case union ha hb =>
    unfold CaptureSet.with_reach
    apply! union
  case var hb hr ih =>
    unfold CaptureSet.with_reach
    apply var_reach (var hb hr)
  case cinstr hb hr ih =>
    unfold CaptureSet.with_reach
    apply cvar_creach (cinstr hb hr)
  case cbound hb hr ih =>
    unfold CaptureSet.with_reach
    apply cvar_creach (cbound hb hr)
  case ckind hb =>
    unfold CaptureSet.with_reach
    apply cvar_creach (ckind hb)
  case label hb =>
    unfold CaptureSet.with_reach
    apply var_reach (label hb)
  case var_reach hr ih =>
    unfold CaptureSet.with_reach
    apply var_reach hr
  case cvar_creach hr ih =>
    unfold CaptureSet.with_reach
    apply cvar_creach hr
  case absurd he =>
    unfold CaptureSet.with_reach
    apply absurd he

theorem ReachSet.with_reach_inv
  (hr : ReachSet Γ C.with_reach R)
  : ReachSet Γ C R := by
  generalize h : C.with_reach = D at hr
  induction hr generalizing C
  case empty =>
    unfold CaptureSet.with_reach at h; split at h <;> simp_all [-Kind.intersect]
    apply empty
  case union ha hb =>
    unfold CaptureSet.with_reach at h; split at h <;> simp_all [-Kind.intersect]
    apply union (ha _) (hb _) <;> aesop
  case var hb hr ih =>
    unfold CaptureSet.with_reach at h; split at h <;> simp_all [-Kind.intersect]
    have ⟨h1, h2⟩ := h; split at h1 <;> simp at h1
  case cinstr hb hr ih =>
    unfold CaptureSet.with_reach at h; split at h <;> simp_all [-Kind.intersect]
    have ⟨h1, h2⟩ := h; split at h1 <;> simp at h1
  case cbound hb hr ih =>
    unfold CaptureSet.with_reach at h; split at h <;> simp_all [-Kind.intersect]
    have ⟨h1, h2⟩ := h; split at h1 <;> simp at h1
  case ckind hb =>
    unfold CaptureSet.with_reach at h; split at h <;> simp_all [-Kind.intersect]
    have ⟨h1, h2⟩ := h; split at h1 <;> simp at h1
  case label =>
    unfold CaptureSet.with_reach at h; split at h <;> simp_all [-Kind.intersect]
    have ⟨h1, h2⟩ := h; split at h1 <;> simp at h1
  case var_reach hr ih =>
    unfold CaptureSet.with_reach at h; split at h <;> simp_all [-Kind.intersect]
    have ⟨h1, h2⟩ := h; split at h1 <;> simp_all
    apply var_reach hr
  case cvar_creach hr ih =>
    unfold CaptureSet.with_reach at h; split at h <;> simp_all [-Kind.intersect]
    have ⟨h1, h2⟩ := h; split at h1 <;> simp_all
    apply cvar_creach hr
  case absurd he =>
    unfold CaptureSet.with_reach at h; split at h <;> simp_all [-Kind.intersect]
    have ⟨h1, h2⟩ := h; split at h1 <;> (subst_vars; simp_all; apply! absurd)

end Capless
