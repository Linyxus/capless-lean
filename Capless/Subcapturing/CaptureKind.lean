import Capless.Subcapturing
import Capless.Inversion.Context

namespace Capless


theorem CaptureKind.union_l_inv (hk : CaptureKind Γ (C1 ∪ C2) K) : CaptureKind Γ C1 K ∧ CaptureKind Γ C2 K := by
  generalize h : C1 ∪ C2 = D at hk
  induction hk generalizing C1 C2 <;> cases h
  case sub hs hk ih =>
    have ⟨_, _⟩ := ih (.refl _)
    apply And.intro <;> apply! sub hs
  case union => apply! And.intro

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
  case singleton_absurd he =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply singleton_absurd
    apply Kind.Subkind.empty_r_inv _ he
    apply Kind.Intersect.with_subkind hs
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

theorem CaptureKind.var_lookup_inv
  (hk : CaptureKind Γ {x=x|L} K)
  (hb : Γ.Bound x S^C)
  : CaptureKind Γ (C.proj L) K ∨ L.IsEmpty := by
  generalize h : {x=x|L} = D at hk
  induction hk <;> cases h
  case var K hb2 hk ih =>
    cases Context.bound_injective hb hb2
    left; assumption
  case label hb2 => cases Context.bound_lbound_absurd hb hb2
  case sub hs hk ih =>
    cases ih hb (.refl _)
    case inl h => left; apply sub hs h
    case inr h => right; assumption
  case singleton_absurd he =>
    right; assumption

theorem CaptureKind.label_lookup_inv
  (hs : CaptureKind Γ {x=x|K1} K)
  (hb : Γ.LBound x c S)
  : (Kind.intersect (.classifier c) K1).Subkind K ∨ K1.IsEmpty := by
  generalize h : {x=x|K1} = D at hs
  induction hs <;> cases h
  case var hb1 hk ih => cases Context.bound_lbound_absurd hb1 hb
  case label hb1 =>
    cases Context.lbound_inj hb hb1; subst_vars
    left; exact .rfl
  case sub hs1 _ ih =>
    cases ih hb (.refl _)
    case inl h => left; apply Kind.Subkind.trans h hs1
    case inr h => right; assumption
  case singleton_absurd he =>
    right; assumption

theorem CaptureKind.cbound_lookup_inv
  (hs : CaptureKind Γ {c=c|L} K)
  (hb : Γ.CBound c (.bound (.upper C)))
  : CaptureKind Γ (C.proj L) K ∨ L.IsEmpty := by
  generalize h : {c=c|L} = D at hs
  induction hs <;> cases h
  case cvar hb2 => cases Context.cbound_injective hb hb2
  case cbound hb2 hk ih =>
    cases Context.cbound_injective hb hb2
    left; assumption
  case cinstr hb2 hk ih => cases Context.cbound_injective hb hb2
  case sub hs hk ih =>
    cases ih hb (.refl _)
    case inl h => left; apply sub hs h
    case inr h => right; assumption
  case singleton_absurd he =>
    right; assumption

theorem CaptureKind.ckind_lookup_inv
  (hs : CaptureKind Γ {c=c|L} K)
  (hb : Γ.CBound c (.bound (.kind K1)))
  : (K1.intersect L).Subkind K ∨ L.IsEmpty := by
  generalize h : {c=c|L} = D at hs
  induction hs <;> cases h
  case cvar hb2 =>
    cases Context.cbound_injective hb hb2
    left; exact .rfl
  case cbound hb2 hk ih => cases Context.cbound_injective hb hb2
  case cinstr hb2 hk ih => cases Context.cbound_injective hb hb2
  case sub hs1 _ ih =>
    cases ih hb (.refl _)
    case inl h => left; apply Kind.Subkind.trans h hs1
    case inr h => right; assumption
  case singleton_absurd he =>
    right; assumption

theorem CaptureKind.cinst_lookup_inv
  (hs : CaptureKind Γ {c=c|L} K)
  (hb : Γ.CBound c (.inst C))
  : CaptureKind Γ (C.proj L) K ∨ L.IsEmpty := by
  generalize h : {c=c|L} = D at hs
  induction hs <;> cases h
  case cvar hb2 => cases Context.cbound_injective hb hb2
  case cbound hb2 hk ih => cases Context.cbound_injective hb hb2
  case cinstr hb2 hk ih =>
    cases Context.cbound_injective hb hb2
    left; assumption
  case sub hs hk ih =>
    cases ih hb (.refl _)
    case inl h => left; apply sub hs h
    case inr h => right; assumption
  case singleton_absurd he =>
    right; assumption

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
    obtain ⟨rfl, rfl⟩ := h
    rename_i p
    cases hk2.var_lookup_inv hb
    case inl h =>
      apply var hb
      apply subkind_proj _ Kind.Intersect.union_r_subkind
      exact ih h hs1 rfl
    case inr he =>
      apply sub hs1
      apply var hb
      have hsub : Kind.Subkind (p.intersect (K1.union K2)) (p.intersect K1) := by
        apply Kind.Subkind.trans Kind.Intersect.union_r_subkind
        apply Kind.Subkind.union_l .rfl
        apply Kind.Subkind.is_empty_l he
      apply subkind_proj hk1 hsub
  case label hb =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    obtain ⟨rfl, rfl⟩ := h
    rename_i p
    cases hk2.label_lookup_inv hb
    case inl h =>
      apply sub
      exact .union_l hs1 (.trans h hs2)
      apply sub Kind.Intersect.union_r_subkind
      apply sub $ Kind.Intersect.with_subkind Kind.Intersect.union_r_subkind
      apply label hb
    case inr he =>
      apply sub hs1
      apply sub (Kind.Intersect.with_subkind (.trans Kind.Intersect.union_r_subkind (.union_l .rfl (.is_empty_l he))))
      apply label hb
  case cvar hb =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    obtain ⟨rfl, rfl⟩ := h
    rename_i p
    cases hk2.ckind_lookup_inv hb
    case inl h =>
      apply sub
      exact .union_l hs1 (.trans h hs2)
      apply sub Kind.Intersect.union_r_subkind
      apply sub $ Kind.Intersect.with_subkind Kind.Intersect.union_r_subkind
      apply cvar hb
    case inr he =>
      apply sub hs1
      apply sub (Kind.Intersect.with_subkind (.trans Kind.Intersect.union_r_subkind (.union_l .rfl (.is_empty_l he))))
      apply cvar hb
  case cbound hb hk1 ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    obtain ⟨rfl, rfl⟩ := h
    rename_i p
    cases hk2.cbound_lookup_inv hb
    case inl h =>
      apply cbound hb
      apply subkind_proj _ Kind.Intersect.union_r_subkind
      apply ih h hs1 (.refl _)
    case inr he =>
      apply sub hs1
      apply cbound hb
      have hsub : Kind.Subkind (p.intersect (K1.union K2)) (p.intersect K1) := by
        apply Kind.Subkind.trans Kind.Intersect.union_r_subkind
        apply Kind.Subkind.union_l .rfl
        apply Kind.Subkind.is_empty_l he
      apply subkind_proj hk1 hsub
  case cinstr hb hk1 ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    obtain ⟨rfl, rfl⟩ := h
    rename_i p
    cases hk2.cinst_lookup_inv hb
    case inl h =>
      apply cinstr hb
      apply subkind_proj _ Kind.Intersect.union_r_subkind
      apply ih h hs1 (.refl _)
    case inr he =>
      apply sub hs1
      apply cinstr hb
      have hsub : Kind.Subkind (p.intersect (K1.union K2)) (p.intersect K1) := by
        apply Kind.Subkind.trans Kind.Intersect.union_r_subkind
        apply Kind.Subkind.union_l .rfl
        apply Kind.Subkind.is_empty_l he
      apply subkind_proj hk1 hsub
  case sub hs hk1 ih =>
    subst_vars
    apply ih hk2
    exact .trans hs hs1
    rfl
  case empty =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    apply empty
  case singleton_absurd he =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    obtain ⟨rfl, rfl⟩ := h
    -- K1 side is empty, so use K2 side
    apply sub hs2
    apply subkind_singleton hk2
    -- p ∩ (K1 ∪ K2) <: (p ∩ K1) ∪ (p ∩ K2) <: p ∩ K2  (since p ∩ K1 is empty)
    apply Kind.Subkind.trans Kind.Intersect.union_r_subkind
    apply Kind.Subkind.union_l (.is_empty_l he) .rfl
  case union ha hb =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    obtain ⟨rfl, rfl⟩ := h
    have ⟨_, _⟩ := hk2.union_l_inv
    apply! union (ha _ _ $ .refl _) (hb _ _ $ .refl _)

theorem CaptureKind.proj_merge_singleton
  (hs1 : CaptureKind Γ (.singleton s K1) K)
  (hs2 : CaptureKind Γ (.singleton s K2) K)
  : CaptureKind Γ (.singleton s (K1.union K2)) K := by
  rw [← Kind.Intersect.top_l (K:=K1)] at hs1
  rw [← Kind.Intersect.top_l (K:=K2)] at hs2
  rw [← CaptureSet.proj] at hs1 hs2
  rw [← Kind.Intersect.top_l (K:=K1.union K2), ← CaptureSet.proj]
  exact proj_merge hs1 hs2 .rfl .rfl

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
  case trans ha hb => aesop
  case singleton_subkind hs =>
    apply! subkind_singleton
  case singleton_absurd L he => apply! singleton_absurd
  case proj_merge =>
    have ⟨_, _⟩ := hk.union_l_inv
    apply! proj_merge_singleton

theorem CaptureKind.absurd {C : CaptureSet n k}
  (he : K.IsEmpty)
  : CaptureKind Γ (C.proj K) L := by
  induction C
  case empty => apply empty
  case union ha hb => apply! union
  case singleton => apply singleton_absurd $ Kind.Intersect.is_empty_r he

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
    case singleton_absurd he => apply! absurd
  case cinstr => apply! cinstr
  case cbound => apply! cbound
  case absurd hk1 he => apply sub _ hk1; apply Kind.Subkind.is_empty_l he
