import Capless.Store
import Capless.Subcapturing
import Capless.Subcapturing.Basic
import Capless.Inversion.Context

/-!
# Basic Properties of Well-Scopedness

This file contains basic properties of the well-scopedness relation.
-/

namespace Capless

theorem WellScoped.subkind
  (hsc : WellScoped Γ cont (.proj C K2))
  (hs : K1.Subkind K2)
  : WellScoped Γ cont (.proj C K1) := by
  generalize h : C.proj K2 = D at hsc
  induction hsc generalizing C K2 K1
  case empty =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    simp; constructor
  case union ha hb =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply! union (ha _ $ .refl _) (hb _ $ .refl _)
  case singleton hb hsc ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply singleton hb
    apply ih
    apply Kind.Intersect.with_subkind hs
    apply! refl
  case csingleton hb hsc ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply csingleton hb
    apply ih
    apply Kind.Intersect.with_subkind hs
    apply! refl
  case cbound hb hsc ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply cbound hb
    apply ih
    apply Kind.Intersect.with_subkind hs
    apply! refl
  case ckind hb ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply! ckind
  case label hb hl =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply! label
  case label_disj hb hd =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply label_disj hb
    apply hd.refine_subkind_l $ Kind.Intersect.with_subkind hs

theorem WellScoped.subkind_singleton
  (hsc : WellScoped Γ cont (.singleton s L))
  (hs : Kind.Subkind K L)
  : WellScoped Γ cont (.singleton s K) := by
  rw [← Kind.Intersect.top_l (K:=L)] at hsc
  have h : CaptureSet.proj (.singleton s .top) L = .singleton s (.intersect .top L) := by simp
  rw [← h] at hsc
  have h1 := hsc.subkind hs
  simp only [CaptureSet.proj] at h1
  rw [Kind.Intersect.top_l] at h1
  assumption

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

theorem WellScoped.cons
  (hsc : WellScoped Γ cont C) :
  WellScoped Γ (Cont.cons u cont) C := by
  induction hsc
  case empty => apply empty
  case union => apply union <;> aesop
  case singleton ih => apply singleton <;> aesop
  case csingleton ih => apply csingleton <;> aesop
  case cbound ih => apply cbound <;> aesop
  case ckind ih => apply ckind <;> aesop
  case label hb hl =>
    apply label hb
    constructor; assumption
  case label_disj hb hd =>
    apply! label_disj

theorem WellScoped.conse
  (hsc : WellScoped Γ cont C) :
  WellScoped Γ (Cont.conse u cont) C := by
  induction hsc
  case empty => apply empty
  case union => apply union <;> aesop
  case singleton ih => apply singleton <;> aesop
  case csingleton ih => apply csingleton <;> aesop
  case cbound ih => apply cbound <;> aesop
  case ckind ih => apply ckind <;> aesop
  case label hb hl =>
    apply label hb
    constructor; assumption
  case label_disj => apply! label_disj

theorem WellScoped.scope
  (hsc : WellScoped Γ cont C) :
  WellScoped Γ (Cont.scope x cont) C := by
  induction hsc
  case empty => apply empty
  case union => apply union <;> aesop
  case singleton ih => apply singleton <;> aesop
  case csingleton ih => apply csingleton <;> aesop
  case cbound ih => apply cbound <;> aesop
  case ckind ih => apply ckind <;> aesop
  case label hb hl =>
    apply label hb
    constructor; assumption
  case label_disj => apply! label_disj


theorem WellScoped.proj_merge
  (hsc1 : WellScoped Γ cont (.proj C K1))
  (hsc2 : WellScoped Γ cont (.proj C K2))
  : WellScoped Γ cont (.proj C (K1.union K2)) := by
  generalize h : C.proj K1 = D at hsc1
  induction hsc1 generalizing C K1 K2
  case empty =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    simp; constructor
  case union ha hb =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    cases hsc2
    apply! union (ha _ $ .refl _) (hb _ $ .refl _)
  case singleton hb hsc ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    cases hsc2
    case singleton hb2 hsc2 =>
      cases Context.bound_injective hb hb2
      apply singleton hb
      apply subkind _ Kind.Intersect.union_r_subkind
      apply! ih _ (.refl _)
    case label hb2 _ => cases Context.bound_lbound_absurd hb hb2
    case label_disj hb2 _ => cases Context.bound_lbound_absurd hb hb2
  case csingleton hb hsc ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    cases hsc2
    case csingleton hb2 hsc2 =>
      cases Context.cbound_injective hb hb2
      apply csingleton hb
      apply subkind _ Kind.Intersect.union_r_subkind
      apply! ih _ (.refl _)
    case cbound hb2 _ => cases Context.cbound_injective hb hb2
    case ckind hb2 => cases Context.cbound_injective hb hb2
  case cbound hb hsc ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    cases hsc2
    case csingleton hb2 _ => cases Context.cbound_injective hb hb2
    case cbound hb2 hsc2 =>
      cases Context.cbound_injective hb hb2
      apply cbound hb
      apply subkind _ Kind.Intersect.union_r_subkind
      apply! ih _ (.refl _)
    case ckind hb2 => cases Context.cbound_injective hb hb2
  case ckind hb =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply! ckind
  case label hb hl =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply! label
  case label_disj hb hd =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    cases hsc2
    case singleton hb2 _ => cases Context.bound_lbound_absurd hb2 hb
    case label hb hl => apply! label
    case label_disj hb2 hd2 =>
      cases Context.lbound_inj hb hb2
      subst_vars
      have h := Kind.Disjoint.union_l hd hd2
      apply subkind_singleton (label_disj hb h) Kind.Intersect.union_r_subkind

theorem WellScoped.proj_merge_singleton
  (hs1 : WellScoped Γ cont (.singleton s K1))
  (hs2 : WellScoped Γ cont (.singleton s K2))
  : WellScoped Γ cont (.singleton s (K1.union K2)) := by
  rw [← Kind.Intersect.top_l (K:=K1)] at hs1
  rw [← Kind.Intersect.top_l (K:=K2)] at hs2
  rw [← CaptureSet.proj] at hs1 hs2
  rw [← Kind.Intersect.top_l (K:=K1.union K2), ← CaptureSet.proj]
  apply! proj_merge

theorem WellScoped.absurd
  (hk : CaptureKind Γ C K)
  (he : K.IsEmpty)
  : WellScoped Γ cont C := by
  induction hk
  case var hb hk ih => apply! singleton hb (ih _)
  case label hl =>
    apply label_disj hl
    apply Kind.Disjoint.symm
    apply Kind.Disjoint.from_empty_intersect Kind.Intersect.lawful he
  case cvar hb => apply ckind hb
  case cbound hb hk ih => apply! cbound hb (ih _)
  case cinstr hb hk ih => apply! csingleton hb (ih _)
  case sub hs hk ih => apply ih; apply hs.empty_r_inv he
  case empty => constructor
  case absurd hk he1 ih => apply! ih
  case union ha hb => simp_all; apply! union


theorem WellScoped.subcapt (hsc : WellScoped Γ cont C2) (hsub : Subcapt Γ C1 C2) : WellScoped Γ cont C1 := by
  induction hsub
  case trans ha hb iha ihb => apply! iha $ ihb _
  case subset hsub => apply! hsc.subset
  case union ha hb iha ihb =>
    apply! union (iha _) (ihb _)
  case var hb => apply! singleton
  case cinstl hb =>
    cases hsc
    case csingleton hb1 _ =>
      cases Context.cbound_injective hb1 hb
      assumption
    case cbound hb1 _ =>
      cases Context.cbound_injective hb1 hb
    case ckind hb1 =>
      cases Context.cbound_injective hb1 hb
  case cinstr hb => apply! csingleton
  case cbound hb => apply! cbound
  case subkind => apply! hsc.subkind_singleton
  case absurd hk he => apply! absurd
  case proj_split =>
    cases hsc
    apply! proj_merge_singleton

theorem WellScoped.var_inv
  (hsc : WellScoped Γ cont {x=x|.top})
  (hbx : Γ.Bound x (S^C)) :
  WellScoped Γ cont C := by
  cases hsc
  case singleton hbx' _ =>
    have h := Context.bound_injective hbx hbx'
    cases h
    rw [CaptureSet.proj_top] at *
    trivial
  case label =>
    exfalso
    apply Context.bound_lbound_absurd <;> easy
  case label_disj =>
    exfalso
    apply Context.bound_lbound_absurd <;> easy

theorem WellScoped.label_inv
  (hsc : WellScoped Γ cont {x=x|.top})
  (hbl : Γ.LBound x c S) :
  ∃ tail, cont.HasLabel x tail := by
  cases hsc
  case singleton =>
    exfalso
    apply Context.bound_lbound_absurd <;> easy
  case label => aesop
  case label_disj hd => cases hd.top_l.is_absurd

end Capless
