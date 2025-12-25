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

theorem WellScoped.cons
  (hsc : WellScoped Γ cont C) :
  WellScoped Γ (Cont.cons u cont) C := by
  induction hsc
  case empty => apply empty
  case union => apply union <;> aesop
  case ckind ih => apply ckind <;> aesop
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
