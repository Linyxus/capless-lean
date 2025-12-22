import Capless.Subcapturing
import Capless.Inversion.Context

namespace Capless


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
  | .absurd hk he => by
    have ⟨_, _⟩ := hk.union_l_inv' heq
    apply And.intro <;> apply! absurd
termination_by structural hk

theorem CaptureKind.union_l_inv (hk : CaptureKind Γ (C1 ∪ C2) K) : CaptureKind Γ C1 K ∧ CaptureKind Γ C2 K := hk.union_l_inv' $ .refl (a := C1 ∪ C2)


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
  case absurd hk he ih =>
    apply absurd
    apply ih hs h
    assumption
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
  : CaptureKind Γ (C.proj L) K := by
  generalize h : {x=x|L} = D at hk
  induction hk <;> cases h
  case var K hb2 hk ih =>
    cases Context.bound_injective hb hb2
    assumption
  case label hb2 => cases Context.bound_lbound_absurd hb hb2
  case sub hs hk ih =>
    apply sub hs
    apply ih hb (.refl _)
  case absurd ih =>
    simp_all
    apply! absurd

theorem CaptureKind.label_lookup_inv
  (hs : CaptureKind Γ {x=x|K1} K)
  (hb : Γ.LBound x c S)
  : (Kind.intersect (.classifier c) K1).Subkind K := by
  generalize h : {x=x|K1} = D at hs
  induction hs <;> cases h
  case var hb1 hk ih => cases Context.bound_lbound_absurd hb1 hb
  case label hb1 =>
    cases Context.lbound_inj hb hb1; subst_vars
    exact .rfl
  case sub hs1 _ ih =>
    apply Kind.Subkind.trans _ hs1
    apply ih hb (.refl _)
  case absurd he hk ih =>
    apply Kind.Subkind.is_empty_l
    apply Kind.Subkind.empty_r_inv _ he
    apply ih hb (.refl _)

theorem CaptureKind.cbound_lookup_inv
  (hs : CaptureKind Γ {c=c|L} K)
  (hb : Γ.CBound c (.bound (.upper C)))
  : CaptureKind Γ (C.proj L) K := by
  generalize h : {c=c|L} = D at hs
  induction hs <;> cases h
  case cvar hb2 => cases Context.cbound_injective hb hb2
  case cbound hb2 hk ih =>
    cases Context.cbound_injective hb hb2
    assumption
  case cinstr hb2 hk ih => cases Context.cbound_injective hb hb2
  case sub hs hk ih =>
    apply sub hs
    apply ih hb (.refl _)
  case absurd he hk ih =>
    apply absurd _ he
    apply ih hb (.refl _)

theorem CaptureKind.ckind_lookup_inv
  (hs : CaptureKind Γ {c=c|L} K)
  (hb : Γ.CBound c (.bound (.kind K1)))
  : (K1.intersect L).Subkind K := by
  generalize h : {c=c|L} = D at hs
  induction hs <;> cases h
  case cvar hb2 =>
    cases Context.cbound_injective hb hb2
    exact .rfl
  case cbound hb2 hk ih => cases Context.cbound_injective hb hb2
  case cinstr hb2 hk ih => cases Context.cbound_injective hb hb2
  case sub hs1 _ ih =>
    apply Kind.Subkind.trans _ hs1
    apply ih hb (.refl _)
  case absurd he hk ih =>
    apply Kind.Subkind.is_empty_l
    apply Kind.Subkind.empty_r_inv _ he
    apply ih hb (.refl _)

theorem CaptureKind.cinst_lookup_inv
  (hs : CaptureKind Γ {c=c|L} K)
  (hb : Γ.CBound c (.inst C))
  : CaptureKind Γ (C.proj L) K := by
  generalize h : {c=c|L} = D at hs
  induction hs <;> cases h
  case cvar hb2 => cases Context.cbound_injective hb hb2
  case cbound hb2 hk ih => cases Context.cbound_injective hb hb2
  case cinstr hb2 hk ih =>
    cases Context.cbound_injective hb hb2
    assumption
  case sub hs hk ih =>
    apply sub hs
    apply ih hb (.refl _)
  case absurd he hk ih =>
    apply absurd _ he
    apply ih hb (.refl _)

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
    apply ih _ (.refl _)
    apply hk2.var_lookup_inv hb
  case label hb =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    have h := hk2.label_lookup_inv hb
    apply sub
    exact .union_l hs1 (.trans h hs2)
    apply sub Kind.Intersect.union_r_subkind
    apply sub $ Kind.Intersect.with_subkind Kind.Intersect.union_r_subkind
    apply label hb
  case cvar hb =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    have h := hk2.ckind_lookup_inv hb
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
    have h := hk2.cbound_lookup_inv hb
    apply ih h (.refl _)
  case cinstr hb hk1 ih =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply cinstr hb
    apply subkind_proj _ Kind.Intersect.union_r_subkind
    have h := hk2.cinst_lookup_inv hb
    apply ih h (.refl _)
  case sub hs hk1 ih =>
    subst_vars
    apply ih hk2
    exact .trans hs hs1
    rfl
  case empty =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    apply empty
  case absurd hk1 he ih =>
    subst_vars
    apply ih hk2 _ (.refl _)
    apply Kind.Subkind.is_empty_l he
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
  case proj_merge =>
    have ⟨_, _⟩ := hk.union_l_inv
    apply! proj_merge_singleton

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
    case absurd he hk ih =>
      apply absurd _ he
      apply ih hb (.refl _)
  case cinstr => apply! cinstr
  case cbound => apply! cbound
  case absurd hk1 he =>
    apply! absurd
