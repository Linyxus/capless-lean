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
  case absurd he hk =>
    have ⟨_, _⟩ := hk.union_l_inv
    apply And.intro <;> apply! absurd

theorem Subcapt.union_l_inv (hs : Subcapt Γ (C1 ∪ C2) D) : Subcapt Γ C1 D ∧ Subcapt Γ C2 D := hs.union_l_inv' $ .refl (a := C1 ∪ C2)

-- Basic operations on .top

theorem CaptureKind.var_top (hb : Γ.Bound x S^C) (hs : CaptureKind Γ C K) : CaptureKind Γ {x=x|.top} K := by
  rw [← CaptureSet.proj_top (C:=C)] at hs
  apply! var

theorem CaptureKind.label_top (hb : Γ.LBound x c S) : CaptureKind Γ {x=x|.top} (.node c []) := by
  rw [← Kind.Intersect.top_r (K:=.node c [])]
  apply label hb

theorem CaptureKind.cvar_top (hb : Γ.CBound c (.bound (.kind K))) : CaptureKind Γ {c=c|.top} K := by
  rw [← Kind.Intersect.top_r (K:=K)]
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

theorem Subcapt.proj_proj_intersect : Subcapt Γ (.proj (.proj C K1) K2) (C.proj (K1.intersect K2)) := by
  induction C
  case empty => simp; apply rfl
  case union ih1 ih2 =>
    simp
    apply! join
  case singleton =>
    simp
    apply singleton_subkind Kind.Intersect.assoc_subkind

theorem Subcapt.proj_intersect_proj : Subcapt Γ (C.proj (K1.intersect K2)) (.proj (.proj C K1) K2) := by
  induction C
  case empty => simp; apply rfl
  case union ih1 ih2 =>
    simp
    apply! join
  case singleton =>
    simp
    apply singleton_subkind Kind.Intersect.assoc_superkind

-- Connections between subkinding and subcapturing


theorem CaptureKind.apply_proj (hk : CaptureKind Γ C K) : CaptureKind Γ (C.proj L) (K.intersect L) := by
  induction hk generalizing L
  case var hb hk ih =>
    apply var hb
    apply subcapt ih .proj_intersect_proj
  case label hb =>
    simp
    apply sub Kind.Intersect.assoc_superkind (label hb)
  case cvar hb =>
    simp
    apply sub Kind.Intersect.assoc_superkind $ cvar hb
  case cbound hb hk ih =>
    apply cbound hb
    apply subcapt ih .proj_intersect_proj
  case cinstr hb hk ih =>
    apply cinstr hb
    apply subcapt ih .proj_intersect_proj
  case sub hs hk ih =>
    apply sub (Kind.Intersect.with_subkind_r hs) ih
  case empty => apply empty
  case singleton_absurd he hk =>
    apply singleton_absurd
    apply Kind.Intersect.is_empty_l hk
  case union ha hb => apply union ha hb

theorem CaptureKind.apply_proj_singleton (hk : CaptureKind Γ (.singleton s .top) K) : CaptureKind Γ (.singleton s L) (K.intersect L) := by
  rw [← Kind.Intersect.top_l (K:=L)]
  rw [← CaptureSet.proj, Kind.Intersect.top_l]
  apply hk.apply_proj

theorem Subcapt.apply_proj (hs : Subcapt Γ C D) : Subcapt Γ (C.proj K) (D.proj K) := by
  induction hs generalizing K
  case trans ha hb => apply trans ha hb
  case subset => apply! subset $ .proj _
  case union ha hb => apply union ha hb
  case var hb =>
    simp
    apply trans (var hb) .proj_intersect_proj
  case cinstl hb =>
    apply trans .proj_proj_intersect
    apply cinstl hb
  case cinstr hb =>
    apply trans (cinstr hb) .proj_intersect_proj
  case cbound hb =>
    apply trans (cbound hb) .proj_intersect_proj
  case absurd hk he =>
    simp
    apply absurd _ he
    apply CaptureKind.sub _ hk.apply_proj
    apply Kind.Intersect.subkind_l

theorem Subcapt.apply_proj_singleton (hs : Subcapt Γ (.singleton s .top) C) : Subcapt Γ (.singleton s K) (C.proj K) := by
  rw [← Kind.Intersect.top_l (K:=K)]
  rw [← CaptureSet.proj, Kind.Intersect.top_l]
  apply! apply_proj
