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
  case singleton s L =>
    apply subkind
    apply! Kind.Intersect.with_subkind
  case union ha hb iha ihb =>
    simp
    apply join iha ihb

theorem Subcapt.proj_l : Subcapt Γ (C.proj K) C := by
  have h := proj_sub (Γ:=Γ) (C:=C) (K1:=K) .of_top
  rw [CaptureSet.proj_top] at h
  assumption

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
termination_by structural hk


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

theorem Subcapt.union_l_inv (hs : Subcapt Γ (C1 ∪ C2) D) : Subcapt Γ C1 D ∧ Subcapt Γ C2 D := hs.union_l_inv' $ .refl (a := C1 ∪ C2)
theorem CaptureKind.union_l_inv (hk : CaptureKind Γ (C1 ∪ C2) K) : CaptureKind Γ C1 K ∧ CaptureKind Γ C2 K := hk.union_l_inv' $ .refl (a := C1 ∪ C2)


theorem Subcapt.proj_absurd_set {C : CaptureSet n k} (he : L.IsEmpty) : Subcapt Γ (C.proj L) .empty := by
  induction C
  case empty => simp; apply rfl
  case union ha hb => apply! union
  case singleton =>
    simp
    apply trans
    apply subkind Kind.Intersect.subkind_r
    apply! proj_absurd

theorem CaptureKind.subset
  (hk : CaptureKind Γ C2 K)
  (hs : C1 ⊆ C2)
  : CaptureKind Γ C1 K := by
  induction hs
  case empty => apply empty
  case rfl => assumption
  case union_l ha hb => apply! union (ha _) (hb _)
  case union_rl ih =>
    have ⟨_, _⟩ := hk.union_l_inv
    apply! ih
  case union_rr ih =>
    have ⟨_, _⟩ := hk.union_l_inv
    apply! ih

theorem CaptureKind.subkind_proj
  (hk : CaptureKind Γ (.proj C K2) K)
  (hs : Kind.Subkind K1 K2)
  : CaptureKind Γ (.proj C K1) K := by
  generalize h : C.proj K2 = D at hk
  induction hk generalizing C K2 K1
  case var hb hk ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply var hb
    apply ih _ (.refl _)
    apply Kind.Intersect.with_subkind hs
  case label hb =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply sub
    apply (Kind.Intersect.with_subkind (Kind.Intersect.with_subkind hs))
    apply! label
  case cvar hb =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply sub
    apply (Kind.Intersect.with_subkind (Kind.Intersect.with_subkind hs))
    apply! cvar
  case cbound hb hk ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply cbound hb
    apply ih _ (.refl _)
    apply Kind.Intersect.with_subkind hs
  case cinstr hb hk ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply cinstr hb
    apply ih _ (.refl _)
    apply Kind.Intersect.with_subkind hs
  case sub hs2 hk ih =>
    subst_vars
    apply sub hs2
    apply ih hs (.refl _)
  case empty =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    apply empty
  case absurd he =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply absurd
    apply Kind.Subkind.of_empty (Kind.Intersect.with_subkind hs) he
  case union ha hb =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply union (ha hs (.refl _)) (hb hs (.refl _))

theorem CaptureKind.subkind_singleton
  (hs : CaptureKind Γ (.singleton s K2) K)
  (hsub : K1.Subkind K2)
  : CaptureKind Γ (.singleton s K1) K := by
  rw [← Kind.Intersect.top_l (K:=K2)] at hs
  rw [← Kind.Intersect.top_l (K:=K1)]
  rw [← CaptureSet.proj] at hs
  rw [← CaptureSet.proj]
  apply! subkind_proj

theorem CaptureKind.absurd_set {C : CaptureSet n k}
  (he : L.IsEmpty)
  : CaptureKind Γ (C.proj L) K := by
  induction C
  case empty => apply empty
  case union ha hb => apply! union
  case singleton => simp; apply absurd; apply Kind.Intersect.is_empty_r he

theorem CaptureKind.var_lookup_inv
  (hk : CaptureKind Γ {x=x|L} K)
  (hb : Γ.Bound x S^C)
  : L.IsEmpty ∨ CaptureKind Γ (C.proj L) K := by
  generalize h : {x=x|L} = D at hk
  induction hk <;> cases h
  case var K hb2 hk ih =>
    cases Context.bound_injective hb hb2
    right; assumption
  case label hb2 => cases Context.bound_lbound_absurd hb hb2
  case sub hs hk ih =>
    cases ih hb (.refl _)
    case inl => left; assumption
    case inr h => right; apply! sub
  case absurd => aesop

theorem CaptureKind.label_lookup_inv
  (hs : CaptureKind Γ {x=x|K1} K)
  (hb : Γ.LBound x c S)
  : K1.IsEmpty ∨ (Kind.intersect (.classifier c) K1).Subkind K := by
  generalize h : {x=x|K1} = D at hs
  induction hs <;> cases h
  case var hb1 hk ih => cases Context.bound_lbound_absurd hb1 hb
  case label hb1 =>
    cases Context.lbound_inj hb hb1; subst_vars
    right; exact .rfl
  case sub hs1 _ ih =>
    cases ih hb (.refl _)
    case inl => aesop
    case inr h => right; exact .trans h hs1
  case absurd => aesop

theorem CaptureKind.cbound_lookup_inv
  (hs : CaptureKind Γ {c=c|L} K)
  (hb : Γ.CBound c (.bound (.upper C)))
  : L.IsEmpty ∨ CaptureKind Γ (C.proj L) K := by
  generalize h : {c=c|L} = D at hs
  induction hs <;> cases h
  case cvar hb2 => cases Context.cbound_injective hb hb2
  case cbound hb2 hk ih =>
    cases Context.cbound_injective hb hb2
    right; assumption
  case cinstr hb2 hk ih => cases Context.cbound_injective hb hb2
  case sub hs hk ih =>
    cases ih hb (.refl _)
    case inl => left; assumption
    case inr h => right; apply! sub
  case absurd => aesop

theorem CaptureKind.ckind_lookup_inv
  (hs : CaptureKind Γ {c=c|L} K)
  (hb : Γ.CBound c (.bound (.kind K1)))
  : L.IsEmpty ∨ (K1.intersect L).Subkind K := by
  generalize h : {c=c|L} = D at hs
  induction hs <;> cases h
  case cvar hb2 =>
    cases Context.cbound_injective hb hb2
    right; exact .rfl
  case cbound hb2 hk ih => cases Context.cbound_injective hb hb2
  case cinstr hb2 hk ih => cases Context.cbound_injective hb hb2
  case sub hs1 _ ih =>
    cases ih hb (.refl _)
    case inl => aesop
    case inr h => right; exact .trans h hs1
  case absurd => aesop

theorem CaptureKind.cinst_lookup_inv
  (hs : CaptureKind Γ {c=c|L} K)
  (hb : Γ.CBound c (.inst C))
  : L.IsEmpty ∨ CaptureKind Γ (C.proj L) K := by
  generalize h : {c=c|L} = D at hs
  induction hs <;> cases h
  case cvar hb2 => cases Context.cbound_injective hb hb2
  case cbound hb2 hk ih => cases Context.cbound_injective hb hb2
  case cinstr hb2 hk ih =>
    cases Context.cbound_injective hb hb2
    right; assumption
  case sub hs hk ih =>
    cases ih hb (.refl _)
    case inl => left; assumption
    case inr h => right; apply! sub
  case absurd => aesop

theorem CaptureKind.proj_merge
  (hk1 : CaptureKind Γ (.proj C K1) L1)
  (hk2 : CaptureKind Γ (.proj C K2) L2)
  (hs1 : L1.Subkind L)
  (hs2 : L2.Subkind L)
  : CaptureKind Γ (.proj C (K1.union K2)) L := by
  generalize h : C.proj K1 = D at hk1
  induction hk1 generalizing C K1 K2
  case var x _ _ _ K hb hk1 ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply var hb
    apply subkind_proj _ Kind.Intersect.union_r_subkind
    cases hk2.var_lookup_inv hb
    case inl h =>
      apply sub hs1
      apply subkind_proj hk1
      apply! Kind.Subkind.union_l .rfl $ .is_empty_l _
    case inr h => apply ih h (.refl _)
  case label hb =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    cases hk2.label_lookup_inv hb
    case inl h =>
      apply sub hs1
      apply subkind_singleton (label hb)
      apply Kind.Intersect.union_r_subkind.trans
      apply Kind.Subkind.union_l .rfl $ .is_empty_l h
    case inr h =>
      apply sub
      exact .union_l hs1 (.trans h hs2)
      apply sub Kind.Intersect.union_r_subkind
      apply sub $ Kind.Intersect.with_subkind Kind.Intersect.union_r_subkind
      apply label hb
  case cvar hb =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    cases hk2.ckind_lookup_inv hb
    case inl h =>
      -- h : (p.intersect K2).IsEmpty
      apply sub hs1
      apply sub $ Kind.Intersect.with_subkind $
        Kind.Subkind.trans Kind.Intersect.union_r_subkind $
        Kind.Subkind.union_l .rfl $ Kind.Subkind.is_empty_l h
      apply cvar hb
    case inr h =>
      -- h : ((p.intersect K2).intersect K).Subkind L2
      apply sub
      exact .union_l hs1 (.trans h hs2)
      apply sub Kind.Intersect.union_r_subkind
      apply sub $ Kind.Intersect.with_subkind Kind.Intersect.union_r_subkind
      apply cvar hb
  case cbound hb hk1 ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply cbound hb
    apply subkind_proj _ Kind.Intersect.union_r_subkind
    cases hk2.cbound_lookup_inv hb
    case inl h =>
      apply sub hs1
      apply subkind_proj hk1
      apply Kind.Subkind.union_l .rfl $ Kind.Subkind.is_empty_l h
    case inr h => apply ih h (.refl _)
  case cinstr hb hk1 ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply cinstr hb
    apply subkind_proj _ Kind.Intersect.union_r_subkind
    cases hk2.cinst_lookup_inv hb
    case inl h =>
      apply sub hs1
      apply subkind_proj hk1
      apply Kind.Subkind.union_l .rfl $ Kind.Subkind.is_empty_l h
    case inr h => apply ih h (.refl _)
  case sub hs hk1 ih =>
    subst_vars
    apply ih hk2
    exact .trans hs hs1
    rfl
  case empty =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    apply empty
  case absurd =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply subkind_singleton
    apply sub hs2 hk2
    apply Kind.Subkind.trans
    . apply Kind.Intersect.union_r_subkind
    . apply Kind.Subkind.union_l _ .rfl
      . apply! Kind.Subkind.is_empty_l
  case union ha hb =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    have ⟨_, _⟩ := hk2.union_l_inv
    apply! union (ha _ $ .refl _) (hb _ $ .refl _)

theorem CaptureKind.proj_merge_singleton
  (hs1 : CaptureKind Γ (.singleton s K1) K)
  (hs2 : CaptureKind Γ (.singleton s K2) K)
  : CaptureKind Γ (.singleton s (K1.union K2)) K := by
  rw [← Kind.Intersect.top_l (K:=K1)] at hs1
  rw [← Kind.Intersect.top_l (K:=K2)] at hs2
  rw [← CaptureSet.proj] at hs1 hs2
  rw [← Kind.Intersect.top_l (K:=K1.union K2), ← CaptureSet.proj]
  exact proj_merge hs1 hs2 .rfl .rfl

theorem CaptureKind.subcapt
  (hk : CaptureKind Γ C2 K)
  (hs : Subcapt Γ C1 C2)
  : CaptureKind Γ C1 K := by
  induction hs generalizing K
  case trans ha hb => apply ha; apply! hb
  case subset => apply! hk.subset
  case union ha hb => apply! union (ha _) (hb _)
  case var hb => apply! var
  case cinstl c C L hb =>
    generalize h : {c=c|L} = D at hk
    induction hk <;> try cases h
    case cvar hb1 => cases Context.cbound_injective hb hb1
    case cbound hb1 hk ih => cases Context.cbound_injective hb hb1
    case cinstr hb1 hk ih => cases Context.cbound_injective hb hb1; assumption
    case sub hs hk ih => apply sub hs; apply ih hb; rfl
    case absurd he => apply! absurd_set
  case cinstr => apply! cinstr
  case cbound => apply! cbound
  case subkind K1 L hs =>
    rw [← Kind.Intersect.top_l (K:=L)] at hk
    rw [← Kind.Intersect.top_l (K:=K1)]
    rw [← CaptureSet.proj] at hk
    rw [← CaptureSet.proj]
    apply subkind_proj hk hs
  case proj_absurd he => apply! absurd
  case proj_split =>
    have ⟨_, _⟩ := hk.union_l_inv
    apply! proj_merge_singleton

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
    apply subkind Kind.Intersect.assoc_subkind

theorem Subcapt.proj_intersect_proj : Subcapt Γ (C.proj (K1.intersect K2)) (.proj (.proj C K1) K2) := by
  induction C
  case empty => simp; apply rfl
  case union ih1 ih2 =>
    simp
    apply! join
  case singleton =>
    simp
    apply subkind Kind.Intersect.assoc_superkind

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
  case absurd he =>
    apply absurd
    apply Kind.Intersect.is_empty_l he
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
  case subkind hs =>
    apply subkind $ Kind.Intersect.with_subkind_r hs
  case proj_absurd he =>
    apply proj_absurd $ Kind.Intersect.is_empty_l he
  case proj_split =>
    simp
    apply proj_split

theorem Subcapt.apply_proj_singleton (hs : Subcapt Γ (.singleton s .top) C) : Subcapt Γ (.singleton s K) (C.proj K) := by
  rw [← Kind.Intersect.top_l (K:=K)]
  rw [← CaptureSet.proj, Kind.Intersect.top_l]
  apply! apply_proj
