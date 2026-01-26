import Capless.Subcapturing
import Capless.Inversion.Context

namespace Capless


theorem CaptureKind.union_l_inv (hk : CaptureKind Γ (C1 ∪ C2) K) : CaptureKind Γ C1 K ∧ CaptureKind Γ C2 K := by
  generalize h : C1 ∪ C2 = D at hk
  induction hk generalizing C1 C2 <;> try cases h
  case sub hs hk ih =>
    have ⟨_, _⟩ := ih (.refl _)
    apply And.intro <;> apply! sub hs
  case union => apply! And.intro
  case reach ih =>
    unfold CaptureSet.with_reach at h; split at h <;> simp_all
    have ⟨_, _⟩ := ih
    apply And.intro <;> apply! reach

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
    have ⟨_, _⟩ := h; subst_vars; simp_all [-Kind.intersect]
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
  case reach ih =>
    have ⟨C0, ha, hb⟩ := CaptureSet.proj_reach_inv h
    have ih := ih hs ha
    rw [hb, CaptureSet.reach_proj]
    apply! reach


theorem CaptureKind.subkind_singleton
  (hs : CaptureKind Γ (.singleton s K2) K)
  (hsub : K1.Subkind K2)
  : CaptureKind Γ (.singleton s K1) K := by
  rw [← Kind.intersect.top_l (K:=K2)] at hs
  rw [← Kind.intersect.top_l (K:=K1)]
  rw [← CaptureSet.proj] at hs
  rw [← CaptureSet.proj]
  apply! subkind_proj

theorem CaptureKind.var_lookup_inv
  (hk : CaptureKind Γ {x=x|L} K)
  (hb : Γ.Bound x S^C)
  : CaptureKind Γ (C.proj L) K ∨ L.IsEmpty := by
  generalize h : {x=x|L} = D at hk
  induction hk <;> try cases h
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
  case reach =>
    unfold CaptureSet.with_reach at h; aesop

theorem CaptureKind.label_lookup_inv
  (hs : CaptureKind Γ {x=x|K1} K)
  (hb : Γ.LBound x c S)
  : (Kind.intersect (.classifier c) K1).Subkind K ∨ K1.IsEmpty := by
  generalize h : {x=x|K1} = D at hs
  induction hs <;> try cases h
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
  case reach =>
    unfold CaptureSet.with_reach at h; aesop

theorem CaptureKind.cbound_lookup_inv
  (hs : CaptureKind Γ {c=c|L} K)
  (hb : Γ.CBound c (.bound (.upper C)))
  : CaptureKind Γ (C.proj L) K ∨ L.IsEmpty := by
  generalize h : {c=c|L} = D at hs
  induction hs <;> try cases h
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
  case reach =>
    unfold CaptureSet.with_reach at h; aesop

theorem CaptureKind.ckind_lookup_inv
  (hs : CaptureKind Γ {c=c|L} K)
  (hb : Γ.CBound c (.bound (.kind K1)))
  : (K1.intersect L).Subkind K ∨ L.IsEmpty := by
  generalize h : {c=c|L} = D at hs
  induction hs <;> try cases h
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
  case reach =>
    unfold CaptureSet.with_reach at h; aesop

theorem CaptureKind.cinst_lookup_inv
  (hs : CaptureKind Γ {c=c|L} K)
  (hb : Γ.CBound c (.inst C))
  : CaptureKind Γ (C.proj L) K ∨ L.IsEmpty := by
  generalize h : {c=c|L} = D at hs
  induction hs <;> try cases h
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
  case reach =>
    unfold CaptureSet.with_reach at h; aesop

@[simp]
private def CaptureSet.drop_reach (s : CaptureSet n k) :=
  match s with
  | empty => empty
  | union a b => union a.drop_reach b.drop_reach
  | singleton s K =>
    let s' : Singleton n k :=
      match s with
      | .var n => .var n
      | .cvar k => .cvar k
      | .reach n => .var n
      | .creach k => .cvar k
    singleton s' K

@[simp]
private theorem CaptureSet.reach_drop_reach {C : CaptureSet n k} : C.with_reach.drop_reach = C.drop_reach := by
  induction C <;> aesop

private theorem CaptureKind.drop_reach
  (hk : CaptureKind Γ C K)
  : CaptureKind Γ C.drop_reach K := by
  induction hk
  case var => apply! var
  case label => apply! label
  case cvar => apply! cvar
  case cbound => apply! cbound
  case cinstr => apply! cinstr
  case sub => apply! sub
  case empty => apply empty
  case singleton_absurd => apply! singleton_absurd
  case union => apply! union
  case reach => aesop

private theorem CaptureKind.drop_reach_inv
  (hk : CaptureKind Γ C.drop_reach K)
  : CaptureKind Γ C K := by
  induction C
  case empty => apply empty
  case union ha hb =>
    have ⟨_, _⟩ := hk.union_l_inv
    apply union <;> aesop
  case singleton s K =>
    simp at hk
    cases s <;> (simp at hk; try assumption)
    . apply reach hk
    . apply reach hk


theorem CaptureKind.with_reach_inv
  (hk : CaptureKind Γ C.with_reach K)
  : CaptureKind Γ C K := by
  have hk1 := hk.drop_reach
  rw [CaptureSet.reach_drop_reach] at hk1
  apply hk1.drop_reach_inv

theorem CaptureKind.proj_merge
  (hk1 : CaptureKind Γ (.proj C K1) L1)
  (hk2 : CaptureKind Γ (.proj C K2) L2)
  (hs1 : L1.Subkind L)
  (hs2 : L2.Subkind L)
  : CaptureKind Γ (.proj C (K1 ++ K2)) L := by
  generalize h : C.proj K1 = D at hk1
  induction hk1 generalizing C K1 K2
  case var x _ _ _ K hb hk1 ih =>
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
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
      have hsub : Kind.Subkind (p.intersect (K1 ++ K2)) (p.intersect K1) := by
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
      have hsub : Kind.Subkind (p.intersect (K1 ++ K2)) (p.intersect K1) := by
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
      have hsub : Kind.Subkind (p.intersect (K1 ++ K2)) (p.intersect K1) := by
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
  case reach hsk ih =>
    have ⟨C0, ha, hb⟩ := CaptureSet.proj_reach_inv h
    subst_vars
    rw [CaptureSet.reach_proj]; apply reach
    apply ih _ hs1 (.refl _)
    rw [CaptureSet.reach_proj] at hk2
    apply hk2.with_reach_inv

theorem CaptureKind.proj_merge_singleton
  (hs1 : CaptureKind Γ (.singleton s K1) K)
  (hs2 : CaptureKind Γ (.singleton s K2) K)
  : CaptureKind Γ (.singleton s (K1 ++ K2)) K := by
  rw [← Kind.intersect.top_l (K:=K1)] at hs1
  rw [← Kind.intersect.top_l (K:=K2)] at hs2
  rw [← CaptureSet.proj] at hs1 hs2
  rw [← Kind.intersect.top_l (K:=K1 ++ K2), ← CaptureSet.proj]
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
  case singleton => apply singleton_absurd $ Kind.intersect.is_empty_r he

theorem CaptureKind.proj_r
  (hk1 : CaptureKind Γ C K)
  (hk2 : CaptureKind Γ (C.proj K) L)
  : CaptureKind Γ C L := by
  induction hk1 generalizing L
  case var hb hk1 ih =>
    apply var hb
    rw [CaptureSet.proj_proj] at ih
    cases hk2.var_lookup_inv hb <;> rename_i hk2
    . apply ih hk2
    . apply ih $ .absurd hk2
  case label hb =>
    apply sub _ (.label hb)
    cases hk2.label_lookup_inv hb <;> rename_i hk2
    . rw [← Kind.intersect.assoc] at hk2
      apply Kind.Subkind.trans _ hk2
      apply Kind.Intersect.subkind_self
    . have hk2 := Kind.Intersect.is_empty_repeat hk2
      apply Kind.Subkind.is_empty_l hk2
  case cvar hb =>
    apply sub _ (.cvar hb)
    cases hk2.ckind_lookup_inv hb <;> rename_i hk2
    . rw [← Kind.intersect.assoc] at hk2
      apply Kind.Subkind.trans _ hk2
      apply Kind.Intersect.subkind_self
    . have hk2 := Kind.Intersect.is_empty_repeat hk2
      apply Kind.Subkind.is_empty_l hk2
  case cbound hb hk ih =>
    apply cbound hb
    rw [CaptureSet.proj_proj] at ih
    cases hk2.cbound_lookup_inv hb <;> rename_i hk2
    . apply ih hk2
    . apply ih $ .absurd hk2
  case cinstr hb hk ih =>
    apply cinstr hb
    rw [CaptureSet.proj_proj] at ih
    cases hk2.cinst_lookup_inv hb <;> rename_i hk2
    . apply ih hk2
    . apply ih $ .absurd hk2
  case sub hsk hk ih =>
    apply ih $ hk2.subkind_proj hsk
  case empty => apply empty
  case singleton_absurd he => apply! singleton_absurd
  case union ha hb iha ihb =>
    have ⟨_, _⟩ := hk2.union_l_inv
    apply! union (iha _) (ihb _)
  case reach ih =>
    rw [CaptureSet.reach_proj] at hk2
    apply reach
    apply ih hk2.with_reach_inv

theorem CaptureKind.reachset
  (hk : CaptureKind Γ C K)
  (hr : ReachSet Γ C R)
  : CaptureKind Γ R K := by
  induction hr
  case empty => apply empty
  case union ha hb =>
    have ⟨_, _⟩ := hk.union_l_inv
    apply! union (ha _) (hb _)
  case var hb hr ih =>
    apply ih
    cases hk.var_lookup_inv hb
    . aesop
    . apply! absurd
  case cinstr hb hr ih =>
    apply ih
    cases hk.cinst_lookup_inv hb
    . aesop
    . apply! absurd
  case cbound hb hr ih =>
    apply ih
    cases hk.cbound_lookup_inv hb
    . aesop
    . apply! absurd
  case ckind hb =>
    cases hk.ckind_lookup_inv hb
    . apply sub _ (reach (cvar hb))
      apply! Kind.Subkind.trans Kind.Intersect.subkind_r
    . apply singleton_absurd
      apply! Kind.intersect.is_empty_r
  case label hb =>
    cases hk.label_lookup_inv hb
    . apply sub _ (label hb)
      apply! Kind.Subkind.trans Kind.Intersect.subkind_r
    . apply singleton_absurd
      apply! Kind.intersect.is_empty_r
  case absurd he => apply empty

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
    case reach => unfold CaptureSet.with_reach at h; aesop
  case cinstr => apply! cinstr
  case cbound => apply! cbound
  case proj_r hk1 => apply! proj_r
  case reach => apply! with_reach_inv
  case reachset hr => apply hk.with_reach_inv.reachset hr

theorem CaptureKind.apply_proj (hk : CaptureKind Γ C K) : CaptureKind Γ (C.proj L) (K.intersect L) := by
  induction hk generalizing L
  case var hb hk ih =>
    simp [-Kind.intersect, CaptureSet.proj_proj] at ih
    apply var hb ih
  case label hb =>
    rw [Kind.intersect.assoc]
    apply label hb
  case cvar hb =>
    rw [Kind.intersect.assoc]
    apply! cvar
  case cbound hb hk ih =>
    simp [-Kind.intersect, CaptureSet.proj_proj] at ih
    apply! cbound hb ih
  case cinstr hb hk ih =>
    simp [-Kind.intersect, CaptureSet.proj_proj] at ih
    apply! cinstr hb ih
  case sub hs hk ih =>
    apply sub (Kind.Intersect.with_subkind_r hs) ih
  case empty => apply empty
  case singleton_absurd he hk =>
    apply singleton_absurd
    apply Kind.intersect.is_empty_l hk
  case union ha hb => apply union ha hb
  case reach ih =>
    rw [CaptureSet.reach_proj]
    apply reach ih

theorem CaptureKind.apply_proj_singleton (hk : CaptureKind Γ (.singleton s .top) K) : CaptureKind Γ (.singleton s L) (K.intersect L) := by
  rw [← Kind.intersect.top_l (K:=L)]
  rw [← CaptureSet.proj, Kind.intersect.top_l]
  apply hk.apply_proj

private theorem Kind.elim_middle_intersect : Subkind (.intersect A (.intersect B C)) (.intersect A C) := by
  rw [Subkind.semantics]
  intro c hc
  have h1 := Intersect.lawful A (B.intersect C)
  have h2 := Intersect.lawful A C
  have h3 := Intersect.lawful B C
  have ⟨_, hr⟩ := h1.contains_inv hc
  have ⟨_, _⟩ := h3.contains_inv hr
  apply! h2.contains

private theorem Kind.elim_last_repeat : Subkind (.intersect A B) (.intersect (.intersect A B) B) := by
  rw [Subkind.semantics]
  intro c hc
  have h1 := Intersect.lawful A B
  have h2 := Intersect.lawful (.intersect A B) B
  have ⟨_, _⟩ := h1.contains_inv hc
  apply! h2.contains

theorem CaptureKind.intersect_with_proj' {C : CaptureSet n k} (hk : CaptureKind Γ (C.proj K) L) : CaptureKind Γ (C.proj K) (L.intersect K) := by
  generalize h : C.proj K = D at hk
  induction hk generalizing C K
  case var hb hk ih =>
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    have ⟨_, _⟩ := h; subst_vars; simp_all [-Kind.intersect]
    apply var hb
    apply sub Kind.elim_middle_intersect $ ih (.refl _)
  case label hb =>
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    have ⟨_, _⟩ := h; subst_vars; simp_all [-Kind.intersect]
    apply sub _ $ label hb
    simp only [← Kind.intersect.assoc]
    apply Kind.elim_last_repeat
  case cvar hb =>
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    have ⟨_, _⟩ := h; subst_vars; simp_all [-Kind.intersect]
    apply sub _ $ cvar hb
    simp only [← Kind.intersect.assoc]
    apply Kind.elim_last_repeat
  case cbound hb hk ih =>
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    have ⟨_, _⟩ := h; subst_vars; simp_all [-Kind.intersect]
    apply cbound hb
    apply sub Kind.elim_middle_intersect $ ih (.refl _)
  case cinstr hb hk ih =>
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    have ⟨_, _⟩ := h; subst_vars; simp_all [-Kind.intersect]
    apply cinstr hb
    apply sub Kind.elim_middle_intersect $ ih (.refl _)
  case sub hsk hk ih =>
    subst_vars
    apply sub _ (ih $ .refl _)
    apply Kind.Intersect.with_subkind_r hsk
  case empty => apply empty
  case singleton_absurd he =>
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    have ⟨_, _⟩ := h; subst_vars; simp_all [-Kind.intersect]
    apply! singleton_absurd
  case union ha hb iha ihb =>
    unfold CaptureSet.proj at h; split at h <;> simp [-Kind.intersect] at h
    have ⟨_, _⟩ := h; subst_vars; simp_all [-Kind.intersect]
    apply union (iha $ .refl _) (ihb $ .refl _)
  case reach ih =>
    have ⟨C0, ha, hb⟩ := CaptureSet.proj_reach_inv h
    have ih := ih ha
    apply! reach


theorem CaptureKind.intersect_with_proj {C : CaptureSet n k} (hk : CaptureKind Γ (C.proj K) L) : CaptureKind Γ (C.proj K) (K.intersect L) := by
  apply sub _ (intersect_with_proj' hk)
  apply Kind.Intersect.subkind_symm
