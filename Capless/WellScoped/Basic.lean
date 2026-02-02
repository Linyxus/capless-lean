import Capless.Store
import Capless.Subcapturing
import Capless.Subcapturing.Basic
import Capless.Inversion.Context
import Capless.WellScoped.ReachSet

/-!
# Basic Properties of Well-Scopedness

This file contains basic properties of the well-scopedness relation.
-/

namespace Capless

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
    exists .singleton (.creach c) (K.intersect L)
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
  case reach hk ih =>
    have ⟨R0, hs0, hr0⟩ := ih he
    exists R0
    apply And.intro hs0 hr0.with_reach

theorem ReachSet.proj_r
  (hk : CaptureKind Γ C K)
  (hr2 : ReachSet Γ (C.proj K) R2)
  : ∃ R ⊆ R2, ReachSet Γ C R := by
  induction hk generalizing R2
  case var hb hk ih =>
    rw [CaptureSet.proj_proj] at ih
    cases hr2
    case var hb2 hr2 =>
      cases Context.bound_injective hb hb2
      have ⟨R, h1, h2⟩ := ih hr2
      exists R; apply And.intro h1
      apply! var
    case label hb2 => cases Context.bound_lbound_absurd hb hb2
    case absurd K he =>
      have ⟨R, h1, h2⟩ := capture_kind_absurd hk.intersect_with_proj he
      exists R; apply And.intro h1
      apply! var
  case label x c _ K hb =>
    exists {x=x|(Kind.classifier c).intersect K}
    apply And.intro _ (.label hb)
    cases hr2
    case var hb2 hr2 => cases Context.bound_lbound_absurd hb2 hb
    case label hb2 =>
      cases Context.lbound_inj hb hb2; subst_vars
      rw [← Kind.intersect.assoc]
      exact .singleton_subkind Kind.Intersect.subkind_self
    case absurd he =>
      exact .singleton_absurd $ Kind.Intersect.is_empty_repeat he
  case cvar c C K hb =>
    exists .singleton (.creach c) (C.intersect K)
    apply And.intro _ (.ckind hb)
    cases hr2
    case ckind hb2 =>
      cases Context.cbound_injective hb hb2
      rw [← Kind.intersect.assoc]
      exact .singleton_subkind Kind.Intersect.subkind_self
    case cinstr hb2 hr2 => cases Context.cbound_injective hb hb2
    case cbound hb2 hr2 => cases Context.cbound_injective hb hb2
    case absurd x c _ K he =>
      exact .singleton_absurd $ Kind.Intersect.is_empty_repeat he
  case cbound hb hk ih =>
    rw [CaptureSet.proj_proj] at ih
    cases hr2
    case ckind hb2 => cases Context.cbound_injective hb hb2
    case cinstr hb2 hr2 => cases Context.cbound_injective hb hb2
    case cbound hb2 hr2 =>
      cases Context.cbound_injective hb hb2
      have ⟨R, h1, h2⟩ := ih hr2
      exists R; apply And.intro h1
      apply! cbound
    case absurd K he =>
      have ⟨R, h1, h2⟩ := capture_kind_absurd hk.intersect_with_proj he
      exists R; apply And.intro h1
      apply! cbound
  case cinstr hb hk ih =>
    rw [CaptureSet.proj_proj] at ih
    cases hr2
    case ckind hb2 => cases Context.cbound_injective hb hb2
    case cbound hb2 hr2 => cases Context.cbound_injective hb hb2
    case cinstr hb2 hr2 =>
      cases Context.cbound_injective hb hb2
      have ⟨R, h1, h2⟩ := ih hr2
      exists R; apply And.intro h1
      apply! cinstr
    case absurd K he =>
      have ⟨R, h1, h2⟩ := capture_kind_absurd hk.intersect_with_proj he
      exists R; apply And.intro h1
      apply! cinstr
  case sub hsk hk ih =>
    have ⟨R3, h3, hr3⟩ := hr2.subkind hsk
    have ⟨R, h, ih⟩ := ih hr3
    exists R
    apply And.intro (.trans h h3) ih
  case empty => cases hr2; exists .empty; apply And.intro .empty .empty
  case singleton_absurd he =>
    exists .empty; apply And.intro .empty (.absurd he)
  case union ha hb iha ihb =>
    cases hr2
    rename_i ha2 hb2
    have ⟨R1, h1, ih1⟩ := iha ha2
    have ⟨R2, h2, ih2⟩ := ihb hb2
    exists R1 ∪ R2
    apply And.intro (.union_monotone h1 h2) (.union ih1 ih2)
  case reach hr ih =>
    rw [CaptureSet.reach_proj] at hr2
    have ⟨R, h, ih⟩ := ih hr2.with_reach_inv
    exists R
    apply And.intro h ih.with_reach

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
  case proj_r hk => apply! proj_r
  case reachsetl hr =>
    have ⟨R1, h1, _, hr1⟩ := hr.idempotent
    exists R1
    apply And.intro (.trans h1 (hr.inj hr2.with_reach_inv)) hr1
  case reachsetr hr =>
    have ⟨R1, _, h1, hr1⟩ := hr.idempotent
    have h2 := hr1.inj hr2
    apply Exists.intro
    apply And.intro (h1.trans h2) hr.with_reach


theorem ReachSet.is_subcapt
  (hr : ReachSet Γ C R)
  : Subcapt Γ C R := by
    apply Subcapt.trans .reach (.reachsetr hr)


theorem WellScoped.subkind {C : CaptureSet n k}
  (hsc : WellScoped Γ cont (C.proj L))
  (hsk : K.Subkind L)
  : WellScoped Γ cont (C.proj K) := by
  generalize h : C.proj L = D at hsc
  induction hsc generalizing C K L
  case empty =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    simp; constructor
  case union ha hb iha ihb =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply! union (iha hsk (.refl _)) (ihb hsk (.refl _))
  case ckind hb =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply! ckind
  case creach hb =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply! creach
  case label hb hl =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply! label
  case label_disj hb hd =>
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    have ⟨_, _⟩ := h; subst_vars
    apply label_disj hb (hd.refine_subkind_l _)
    apply Kind.Intersect.with_subkind hsk
  case absurd he =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply absurd
    apply Kind.Subkind.empty_r_inv _ he
    apply Kind.Intersect.with_subkind hsk

theorem WellScoped.singleton_subkind
  (hsc : WellScoped Γ cont (.singleton s L))
  (hs : Kind.Subkind K L)
  : WellScoped Γ cont (.singleton s K) := by
  rw [← Kind.intersect.top_l (K:=L)] at hsc
  have h : CaptureSet.proj (.singleton s .top) L = .singleton s (.intersect .top L) := by simp
  rw [← h] at hsc
  have h1 := hsc.subkind hs
  simp only [CaptureSet.proj] at h1
  rw [Kind.intersect.top_l] at h1
  exact h1

theorem WellScoped.proj_merge' {C : CaptureSet n k}
  (hsc1 : WellScoped Γ cont (C.proj K))
  (hsc2 : WellScoped Γ cont (C.proj L))
  : WellScoped Γ cont (C.proj (K ++ L)) := by
  generalize h : C.proj K = D at hsc1
  induction hsc1 generalizing C K L
  case empty =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    apply empty
  case union ha hb =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    cases hsc2
    apply! union (ha _ (.refl _)) (hb _ (.refl _))
  case ckind hb =>
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    have ⟨_, _⟩ := h; subst_vars
    apply! ckind
  case creach hb =>
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    have ⟨_, _⟩ := h; subst_vars
    apply! creach
  case label hb hl =>
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    have ⟨_, _⟩ := h; subst_vars
    apply! label
  case label_disj hb hd =>
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    have ⟨_, _⟩ := h; subst_vars
    cases hsc2
    case label hb2 hl =>
      cases Context.lbound_inj hb hb2; subst_vars
      apply! label
    case label_disj hb2 hd2 =>
      cases Context.lbound_inj hb hb2; subst_vars
      apply label_disj hb
      apply Kind.Disjoint.refine_subkind_l (.union_l hd hd2) Kind.Intersect.union_r_subkind
    case absurd he =>
      apply label_disj hb
      apply Kind.Disjoint.refine_subkind_l (.union_l hd $ Kind.Disjoint.is_empty_l he) Kind.Intersect.union_r_subkind
  case absurd he =>
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    have ⟨_, _⟩ := h; subst_vars
    apply singleton_subkind hsc2 (.trans Kind.Intersect.union_r_subkind _)
    apply Kind.Subkind.union_l (.is_empty_l he) .rfl

theorem WellScoped.proj_merge
  (hsc1 : WellScoped Γ cont (.singleton s K))
  (hsc2 : WellScoped Γ cont (.singleton s L))
  : WellScoped Γ cont (.singleton s (K ++ L)) := by
  rw [← Kind.intersect.top_l (K:=K), ← CaptureSet.proj] at hsc1
  rw [← Kind.intersect.top_l (K:=L), ← CaptureSet.proj] at hsc2
  rw [← Kind.intersect.top_l (K:=K++L), ← CaptureSet.proj]
  apply! proj_merge'

theorem WellScoped.subset {C1 C2 : CaptureSet n k}
  (hsc : WellScoped Γ cont C2)
  (hs : C1.Subset C2) : WellScoped Γ cont C1 := by
  induction hs
  case empty => apply empty
  case rfl => assumption
  case union_l ha hb iha ihb =>
    apply! union (iha _) (ihb _)
  case union_rl ha iha =>
    cases hsc
    apply! iha
  case union_rr ha iha =>
    cases hsc
    apply! iha
  case singleton_subkind => apply! singleton_subkind
  case singleton_absurd => apply! absurd
  case proj_merge =>
    cases hsc
    apply! proj_merge
  case trans ha hb =>
    apply ha; apply! hb
  case var_reach =>
    cases hsc; apply! absurd
  case cvar_creach =>
    cases hsc
    case creach => apply! ckind
    case absurd => apply! absurd

theorem WellScoped.cons
  (hsc : WellScoped Γ cont C) :
  WellScoped Γ (Cont.cons u cont) C := by
  induction hsc
  case empty => apply empty
  case union => apply union <;> aesop
  case ckind ih => apply ckind <;> aesop
  case creach ih => apply creach <;> aesop
  case label hb hl =>
    apply label hb
    constructor; assumption
  case label_disj hb hd =>
    apply! label_disj
  case absurd => apply! absurd

theorem WellScoped.conse
  (hsc : WellScoped Γ cont C) :
  WellScoped Γ (Cont.conse u cont) C := by
  induction hsc
  case empty => apply empty
  case union => apply union <;> aesop
  case ckind ih => apply ckind <;> aesop
  case creach ih => apply creach <;> aesop
  case label hb hl =>
    apply label hb
    constructor; assumption
  case label_disj => apply! label_disj
  case absurd => apply! absurd

theorem WellScoped.scope
  (hsc : WellScoped Γ cont C) :
  WellScoped Γ (Cont.scope x cont) C := by
  induction hsc
  case empty => apply empty
  case union => apply union <;> aesop
  case ckind ih => apply ckind <;> aesop
  case creach ih => apply creach <;> aesop
  case label hb hl =>
    apply label hb
    constructor; assumption
  case label_disj => apply! label_disj
  case absurd => apply! absurd

-- Inversions

theorem ReachSet.var_inv
  (hr : ReachSet Γ {x=x|.top} R)
  (hbx : Γ.Bound x (S^C))
  : ∃ R' ⊆ R, ReachSet Γ C R' := by
  cases hr
  case var hb hr =>
    cases Context.bound_injective hb hbx
    rw [CaptureSet.proj_top] at hr
    exists R; apply And.intro .rfl hr
  case label hb => cases Context.bound_lbound_absurd hbx hb
  case absurd he => contrapose he; decide

theorem ReachSet.label_inv
  (hr : ReachSet Γ {x=x|.top} R)
  (hsc : WellScoped Γ cont R)
  (hbx : Γ.LBound x c S)
  : ∃ tail, cont.HasLabel x tail := by
  cases hr
  case var hb hr => cases Context.bound_lbound_absurd hb hbx
  case label hb =>
    cases Context.lbound_inj hb hbx; subst_vars
    cases hsc
    case label tail hb hl =>
      cases Context.lbound_inj hb hbx; subst_vars
      exists tail
    case label_disj hb he =>
      cases Context.lbound_inj hb hbx; subst_vars
      rw [Kind.intersect.top_r] at he
      cases he.with_self.is_absurd
    case absurd he =>
      rw [Kind.intersect.top_r] at he
      cases he.is_absurd
  case absurd he => cases he.is_absurd

end Capless
