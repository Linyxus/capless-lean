import Capless.Subcapturing
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

theorem Subcapt.proj_sub {C : CaptureSet n k}
  (hsk : K1.Subkind K2)
  : Subcapt Γ (C.proj K1) (C.proj K2) := by
  induction C
  case empty => simp; apply subset .rfl
  case singleton s => apply singleton_proj_sub hsk
  case union ha hb iha ihb =>
    simp
    apply join iha ihb

theorem Subcapt.proj_l : Subcapt Γ (C.proj K) C := by
  induction C
  case empty => simp; apply rfl
  case singleton => apply singleton_proj_l
  case union ha hb iha ihb =>
    simp
    apply! join

-- theorem CaptureKind.var (hb : Context.Bound Γ x (S^C)) (hk : CaptureKind Γ C K) : CaptureKind Γ {x=x} K := by
--   apply csub
--   apply Subcapt.var hb
--   assumption

theorem CaptureKind.union_l_inv' (hk : CaptureKind Γ C K) (heq : C = C1 ∪ C2) : CaptureKind Γ C1 K ∧ CaptureKind Γ C2 K :=
  match hk with
  | .cvar _ => by cases heq
  | .union ha hb => by
    injections
    subst_vars
    apply! And.intro
  | .sub hsk hk => by
    have ⟨_, _⟩ := hk.union_l_inv' heq
    apply And.intro <;> apply! CaptureKind.sub
  | .empty => by cases heq
  | .singleton_proj_kind => by cases heq
  | .singleton_proj hk => by cases heq
termination_by structural hk


-- mutual
theorem Subcapt.union_l_inv' (hs : Subcapt Γ C D) (heq : C = (C1 ∪ C2)) : Subcapt Γ C1 D ∧ Subcapt Γ C2 D :=
  match hs with
  | .trans ha hb => by
    have ⟨_, _⟩ := ha.union_l_inv' heq
    apply And.intro <;> apply! Subcapt.trans _
  | .subset hsub => by
    rw [heq] at hsub
    have ⟨_, _⟩ := CaptureSet.Subset.union_l_inv hsub
    apply And.intro <;> apply! Subcapt.subset
  | .union ha hb => by
    injections
    subst_vars
    apply And.intro ha hb
  | .cinstl hb => by
    subst_vars
    have h1 : Subcapt Γ C1 (C1 ∪ C2) := Subcapt.subset $ .union_rl .rfl
    have h2 : Subcapt Γ C2 (C1 ∪ C2) := Subcapt.subset $ .union_rr .rfl
    apply And.intro <;> apply! Subcapt.trans _ (.cinstl hb)
  | .proj_r hs hk => by
    have ⟨_, _⟩ := hs.union_l_inv' heq
    have ⟨_, _⟩ := hk.union_l_inv' heq
    apply And.intro <;> apply! Subcapt.proj_r
termination_by structural hs
-- end

theorem Subcapt.union_l_inv (hs : Subcapt Γ (C1 ∪ C2) D) : Subcapt Γ C1 D ∧ Subcapt Γ C2 D := hs.union_l_inv' $ .refl (a := C1 ∪ C2)
theorem CaptureKind.union_l_inv (hk : CaptureKind Γ (C1 ∪ C2) K) : CaptureKind Γ C1 K ∧ CaptureKind Γ C2 K := hk.union_l_inv' $ .refl (a := C1 ∪ C2)

theorem CaptureKind.proj_kind : CaptureKind Γ (.proj C K) K := by
  induction C
  case empty => apply empty
  case union  => apply! union
  case singleton => apply! singleton_proj_kind

theorem CaptureKind.proj (hk : CaptureKind Γ C K) : CaptureKind Γ (C.proj K1) K := by
  induction C
  case empty => simp; apply empty
  case union ha hb =>
    have ⟨_, _⟩ := hk.union_l_inv
    apply! union (ha _) (hb _)
  case singleton => apply! singleton_proj


theorem Subcapt.proj (hs : Subcapt Γ C1 C2) : Subcapt Γ (C1.proj K) (C2.proj K) := by
  apply proj_r
  apply trans .proj_l hs
  apply CaptureKind.proj_kind

theorem Subcapt.proj_disj
  (hd : Kind.Disjoint K1 K2)
  (hk : CaptureKind Γ C K1)
  : Subcapt Γ (C.proj K2) .empty := by
  induction C
  case empty => simp; apply rfl
  case union ha hb =>
    simp
    have ⟨_, _⟩ := hk.union_l_inv
    apply! union (ha _) (hb _)
  case singleton => apply! singleton_proj_disj

-- theorem CaptureKind.proj_disj  (hk : CaptureKind Γ C K1) (hd : Kind.Disjoint K1 K2) : CaptureKind Γ (C.proj K2) K3 := by
--   induction C
--   case empty => simp; apply empty
--   case union ha hb iha ihb =>
--     simp
--     have ⟨_, _⟩ := hk.union_l_inv
--     apply! union (iha _) (ihb _)
--   case singleton => apply! singleton_proj_disj






end Capless
