import Capless.Subcapturing
import Capless.Subcapturing.CaptureKind
import Capless.Inversion.Context

/-!
# Basic Properties of Subcapturing

This file contains basic properties of the subcapturing relation.
-/

namespace Capless

theorem Subcapt.rfl :
  Subcapt Γ C C := by
  apply subset
  apply CaptureSet.Subset.rfl

theorem Subcapt.join
  (h1 : Γ ⊢ C1 <:c D1)
  (h2 : Γ ⊢ C2 <:c D2) :
  Γ ⊢ C1 ∪ C2 <:c D1 ∪ D2 := by
  apply Subcapt.union
  { apply Subcapt.trans; exact h1
    apply Subcapt.subset; apply CaptureSet.Subset.union_rl; apply CaptureSet.Subset.rfl }
  { apply Subcapt.trans; exact h2
    apply Subcapt.subset; apply CaptureSet.Subset.union_rr; apply CaptureSet.Subset.rfl }

theorem Subcapt.subkind {C : CaptureSet n k}
  (hs : K.Subkind L) :
  (Subcapt Γ (C.proj K) (C.proj L)) := by
  apply subset
  apply CaptureSet.Subset.subkind hs

theorem Subcapt.singleton_subkind
  (hs : K.Subkind L) :
  Subcapt Γ (.singleton s K) (.singleton s L) := by
  apply subset $ .singleton_subkind hs

theorem Subcapt.union_l_inv' (hs : Subcapt Γ C D) (heq : C = (C1 ∪ C2)) : Subcapt Γ C1 D ∧ Subcapt Γ C2 D := by
  induction hs <;> (subst_vars; try simp_all)
  case trans ha hb iha ihb =>
    have ⟨_, _⟩ := ihb
    apply And.intro <;> apply! trans
  case subset hsub =>
    have ⟨_, _⟩ := hsub.union_l_inv
    apply And.intro <;> apply! subset
  case cinstl Γ _ hb =>
    unfold CaptureSet.proj at heq; split at heq <;> simp at heq
    have ⟨_, _⟩ := heq; subst_vars; simp_all
    rename_i Γ c L _ C1 C2
    have h1 : Subcapt Γ (C1.proj L) ((C1 ∪ C2).proj L) := by
      simp
      apply Subcapt.subset $ .union_rl .rfl
    have h2 : Subcapt Γ (C2.proj L) ((C1 ∪ C2).proj L) := by
      simp
      apply Subcapt.subset $ .union_rr .rfl
    apply And.intro <;> apply! trans _ (.cinstl hb)
  case union =>
    injections; subst_vars; apply And.intro <;> assumption
  case proj_r hk =>
    have ⟨_, _⟩ := hk.union_l_inv
    apply And.intro
    . apply! trans (.proj_r _) (.subset $ .union_rl .rfl)
    . apply! trans (.proj_r _) (.subset $ .union_rr .rfl)
  case absurd he hk =>
    have ⟨_, _⟩ := hk.union_l_inv
    apply And.intro <;> apply! absurd

theorem Subcapt.union_l_inv (hs : Subcapt Γ (C1 ∪ C2) D) : Subcapt Γ C1 D ∧ Subcapt Γ C2 D := hs.union_l_inv' $ .refl (a := C1 ∪ C2)

-- Basic operations on .top

theorem CaptureKind.var_top (hb : Γ.Bound x S^C) (hs : CaptureKind Γ C K) : CaptureKind Γ {x=x|.top} K := by
  rw [← CaptureSet.proj_top (C:=C)] at hs
  apply! var

theorem CaptureKind.label_top (hb : Γ.LBound x c S) : CaptureKind Γ {x=x|.top} (.node c []) := by
  rw [← Kind.intersect.top_r (K:=.node c [])]
  apply label hb

theorem CaptureKind.cvar_top (hb : Γ.CBound c (.bound (.kind K))) : CaptureKind Γ {c=c|.top} K := by
  rw [← Kind.intersect.top_r (K:=K)]
  apply cvar hb

theorem CaptureKind.cbound_top (hb : Γ.CBound c (.bound (.upper C))) (hs : CaptureKind Γ C K) : CaptureKind Γ {c=c|.top} K := by
  rw [← CaptureSet.proj_top (C:=C)] at hs
  apply! cbound

theorem CaptureKind.cinstr_top (hb : Γ.CBound c (.inst C)) (hs : CaptureKind Γ C K) : CaptureKind Γ {c=c|.top} K := by
  rw [← CaptureSet.proj_top (C:=C)] at hs
  apply! cinstr

theorem Subcapt.var_top (hb : Γ.Bound x S^C) : Subcapt Γ {x=x|.top} C := by
  have h := Subcapt.var hb (L:=.top)
  rw [CaptureSet.proj_top] at h
  exact h

theorem Subcapt.cinstl_top (hb : Γ.CBound c (.inst C)) : Subcapt Γ C {c=c|.top} := by
  have h := Subcapt.cinstl hb (L:=.top)
  rw [CaptureSet.proj_top] at h
  exact h

theorem Subcapt.cinstr_top (hb : Γ.CBound c (.inst C)) : Subcapt Γ {c=c|.top} C := by
  have h := Subcapt.cinstr hb (L:=.top)
  rw [CaptureSet.proj_top] at h
  exact h

theorem Subcapt.cbound_top (hb : Γ.CBound c (.bound (.upper C))) : Subcapt Γ {c=c|.top} C := by
  have h := Subcapt.cbound hb (L:=.top)
  rw [CaptureSet.proj_top] at h
  exact h

-- Connections between subkinding and subcapturing

theorem Subcapt.apply_proj (hs : Subcapt Γ C D) : Subcapt Γ (C.proj K) (D.proj K) := by
  induction hs generalizing K
  case trans ha hb => apply trans ha hb
  case subset => apply! subset $ .proj _
  case union ha hb => apply union ha hb
  case var hb =>
    simp [-Kind.intersect, CaptureSet.proj_proj]
    apply! var
  case cinstl hb =>
    rw [CaptureSet.proj_proj, CaptureSet.proj]
    apply! cinstl
  case cinstr hb =>
    simp [-Kind.intersect, CaptureSet.proj_proj]
    apply! cinstr
  case cbound hb =>
    simp [-Kind.intersect, CaptureSet.proj_proj]
    apply! cbound
  case proj_r hk =>
    apply trans
    . apply proj_r (.sub Kind.Intersect.subkind_l hk.apply_proj)
    . simp only [CaptureSet.proj_proj]
      apply subset (.subkind _)
      apply Kind.Intersect.subkind_symm
  case absurd hk he =>
    simp
    apply absurd _ he
    apply CaptureKind.sub _ hk.apply_proj
    apply Kind.Intersect.subkind_l

theorem Subcapt.apply_proj_singleton (hs : Subcapt Γ (.singleton s .top) C) : Subcapt Γ (.singleton s K) (C.proj K) := by
  rw [← Kind.intersect.top_l (K:=K)]
  rw [← CaptureSet.proj, Kind.intersect.top_l]
  apply! apply_proj
