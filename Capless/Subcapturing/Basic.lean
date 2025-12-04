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

inductive Instantiated : Context n m k -> CaptureSet n k -> CaptureSet n k -> Prop where
  | rfl : Instantiated Γ C C
  | trans : Instantiated Γ C1 C2 -> Instantiated Γ C2 C3 -> Instantiated Γ C1 C3
  | csubst : Γ.CBound c (.inst C) -> Instantiated Γ {c=c} C
  | union : Instantiated Γ C1 D1 -> Instantiated Γ C2 D2 -> Instantiated Γ (C1 ∪ C2) (D1 ∪ D2)

theorem Instantiated.empty (hi : Instantiated Γ .empty C) : C = .empty := by
  generalize h : CaptureSet.empty = D at hi
  induction hi <;> (subst_vars; simp_all)

theorem Instantiated.union_inv (hi : Instantiated Γ (C1 ∪ C2) D) : ∃ D1 D2, D = D1 ∪ D2 ∧ Instantiated Γ C1 D1 ∧ Instantiated Γ C2 D2 := by
  generalize h : (C1 ∪ C2) = C at hi
  induction hi generalizing C1 C2 <;> (subst_vars; simp_all)
  case rfl => apply And.intro <;> apply rfl
  case trans ha hb =>
    have ⟨D1, D2, hb1, hb2, hb3⟩ := hb
    subst_vars
    rename_i ih
    have ⟨E1, E2, ha1, ha2, ha3⟩ := ih $ .refl _
    exists E1, E2
    apply And.intro; assumption
    apply And.intro <;> apply! trans

theorem Instantiated.singleton_var_eq (hi : Instantiated Γ {x=x} C1) : C1 = {x=x} := by
  generalize heq : ({x=x} : CaptureSet _ _) = D at hi
  induction hi
  case rfl => simp_all
  case trans ih1 ih2 =>
    subst heq
    rw [ih1 (.refl _)] at ih2
    exact ih2 (.refl _)
  case csubst => simp [CaptureSet.singleton, Singleton.var, Singleton.cvar] at heq
  case union => simp [CaptureSet.singleton] at heq

theorem Instantiated.singleton_proj_eq (hi : Instantiated Γ (.singleton (.proj s K)) C1) : C1 = .singleton (.proj s K) := by
  generalize heq : (CaptureSet.singleton (.proj s K)) = D at hi
  induction hi
  case rfl => simp_all
  case trans ih1 ih2 =>
    subst heq
    rw [ih1 (.refl _)] at ih2
    exact ih2 (.refl _)
  case csubst => simp [CaptureSet.singleton, Singleton.proj, Singleton.cvar] at heq
  case union => simp [CaptureSet.singleton] at heq

theorem Instantiated.singleton_var_inv (hi : Instantiated Γ {x=x} C1) : {x=x} ⊆ C1 := by
  rw [hi.singleton_var_eq]; apply CaptureSet.Subset.rfl

theorem Instantiated.subset_has_var (hi : Instantiated Γ C C1) (hc : {x=x} ⊆ C1) (hs1 : C ⊆ D) : ∃ D1, Instantiated Γ D D1 ∧ {x=x} ⊆ D1 := by
  induction hs1 generalizing C1
  case empty => cases hi.empty; cases hc
  case rfl => exists C1
  case union_l ha hb =>
    have ⟨D1, D2, _, hl, hr⟩ := hi.union_inv
    subst_vars; simp_all
    cases hc
    case union_rl hc =>
      have ⟨E1, _, _⟩ := ha hl hc
      exists E1
    case union_rr hc =>
      have ⟨E1, _, _⟩ := hb hr hc
      exists E1
  case union_rl R1 R2 _ ha =>
    have ⟨D1, hi, hs⟩ := ha hi hc
    exists (D1 ∪ R2)
    apply And.intro; apply! union _ .rfl ; apply! CaptureSet.Subset.union_rl
  case union_rr R1 R2 _ ha =>
    have ⟨D1, hi, hs⟩ := ha hi hc
    exists (R2 ∪ D1)
    apply And.intro; apply! union .rfl ; apply! CaptureSet.Subset.union_rr

theorem Subcapt.var_inv'
  (hs : Subcapt Γ C1 D)
  (hsub : Instantiated Γ C1 C2 ∧ {x=x} ⊆ C2)
  (hb : Γ.Bound x S^C) : (∃ D1, Instantiated Γ D D1 ∧ {x=x} ⊆ D1) ∨ (Subcapt Γ C D) := by
  induction hs
  case trans h1 h2 ih1 ih2 =>
    cases ih1 hsub hb
    case inl ih1 =>
      have ⟨D1, ha1⟩ := ih1
      apply! ih2
    case inr ih1 => right; apply! trans
  case subset hs =>
    have ⟨hi, hsx⟩ := hsub
    left
    apply! hi.subset_has_var
  case union iha ihb =>
    have ⟨hi, hsx⟩ := hsub
    have ⟨D1, D2, _, hl, hr⟩ := hi.union_inv
    subst_vars
    cases hsx
    case union_rl hsx => apply iha (And.intro hl hsx) hb
    case union_rr hsx => apply ihb (And.intro hr hsx) hb
  case var hb1 =>
    have ⟨hi, hsx⟩ := hsub
    -- hi : Instantiated Γ {x'=x'} C2, hsx : {x=x} ⊆ C2
    -- From singleton_var_eq: C2 = {x'=x'}
    rw [hi.singleton_var_eq] at hsx
    -- hsx : {x=x} ⊆ {x'=x'}, so x = x'
    cases hsx
    case rfl =>
      -- x = x', so hb and hb1 are about the same variable
      cases Context.bound_injective hb hb1
      -- C = C' (the capture sets are equal)
      right
      apply Subcapt.rfl
  case cinstl hcb =>
    -- C1 = C' for some capture set, D = {c=c}
    -- We need to show {x=x} is in D's instantiation or Subcapt Γ C D
    have ⟨hi, hsx⟩ := hsub
    left
    -- D = {c=c}, and we have hcb : CBound c (inst C')
    -- Instantiated Γ {c=c} C' via csubst, then Instantiated Γ C' C2 via hi
    -- So Instantiated Γ {c=c} C2 via trans
    exists C2
    constructor
    · exact .trans (.csubst hcb) hi
    · exact hsx
  case cinstr hcb =>
    -- C1 = {c=c}, D = C' (the instantiated capture set)
    have ⟨hi, hsx⟩ := hsub
    left
    -- hi : Instantiated Γ {c=c} C2, hsx : {x=x} ⊆ C2
    -- D = C', we need Instantiated Γ C' D1 and {x=x} ⊆ D1
    -- We can use C2 as D1 if we can show Instantiated Γ C' C2
    -- But hi goes from {c=c} to C2, not from C' to C2
    -- However, {c=c} instantiates to C' via csubst, so hi factors through C'
    -- Let's just use rfl on C' and show {x=x} ⊆ C' via hi
    sorry
  case cbound hcb =>
    -- C1 = {c=c}, D = C' (the upper bound)
    have ⟨hi, hsx⟩ := hsub
    -- Similar issue - we need to relate hi to instantiation of D
    sorry
  case singleton_proj_sub hsk =>
    have ⟨hi, hsx⟩ := hsub
    -- C1 = singleton (s.proj K1), D = singleton (s.proj K2)
    -- hi : Instantiated Γ (singleton (s.proj K1)) C2
    -- By singleton_proj_eq, C2 = singleton (s.proj K1)
    rw [hi.singleton_proj_eq] at hsx
    -- Now hsx : {x=x} ⊆ singleton (s.proj K1)
    -- {x=x} = singleton (var x), singleton (s.proj K1) = singleton (proj s K1)
    -- These can only be equal via rfl if var x = proj s K1, which is impossible
    -- Lean can figure this out automatically with cases
    cases hsx
  case singleton_proj_l =>
    have ⟨hi, hsx⟩ := hsub
    -- C1 = singleton (s.proj K), D = singleton s
    rw [hi.singleton_proj_eq] at hsx
    cases hsx
  case proj_r hs hk ih =>
    have ⟨hi, hsx⟩ := hsub
    cases ih hsub hb
    case inl h =>
      left
      have ⟨D1, hd1, hd2⟩ := h
      sorry
    case inr h =>
      right
      apply Subcapt.trans h
      apply Subcapt.proj_r .rfl
      sorry -- Need CaptureKind Γ D K, but we only have CaptureKind Γ C K
  case singleton_proj_disj hd hk =>
    have ⟨hi, hsx⟩ := hsub
    -- C1 = singleton (s.proj K2), D = .empty
    -- By singleton_proj_eq, C2 = singleton (s.proj K2)
    rw [hi.singleton_proj_eq] at hsx
    -- hsx : {x=x} ⊆ singleton (s.proj K2) is impossible
    cases hsx





theorem CaptureKind.var_inv' (hk : CaptureKind Γ D K) (heq : D = {x=x}) (hb : Γ.Bound x S^C) : CaptureKind Γ C K := by
  induction hk <;> (subst_vars; try simp_all)
  case var hb1 hk ih =>
    cases Context.bound_injective hb hb1
    assumption
  case label hb1 => cases Context.bound_lbound_absurd hb hb1
  case sub hsk hk ih => apply! sub

theorem CaptureKind.var_inv (hk : CaptureKind Γ {x=x} K) (hb : Γ.Bound x S^C) : CaptureKind Γ C K := by apply! hk.var_inv' (.refl _)

-- theorem CaptureKind.proj_inv' (hk : CaptureKind Γ D K) (heq : D = C.proj K1) : K1.Subkind K ∨ (∃ K2, K1.Disjoint K2 ∧ CaptureKind Γ C K2) ∨ CaptureKind Γ C K := by
--   induction hk generalizing C K1
--   case var hb hk ih =>
--     unfold CaptureSet.proj at heq; split at heq <;> simp at heq
--   case label hb ih =>
--     unfold CaptureSet.proj at heq; split at heq <;> simp at heq
--   case cvar =>
--     unfold CaptureSet.proj at heq; split at heq <;> simp at heq
--   case cbound =>
--     unfold CaptureSet.proj at heq; split at heq <;> simp at heq
--   case cinstr =>
--     unfold CaptureSet.proj at heq; split at heq <;> simp at heq
--   case sub hsk hk ih =>
--     cases ih heq
--     case inl hsk1 => left; apply hsk1.trans hsk
--     case inr h =>
--       cases h
--       case inl hd =>
--         obtain ⟨K2, hd, hk2⟩ := hd
--         -- K1.Disjoint K2 and CaptureKind Γ C K2, we have hsk : K' -> K
--         -- We need to show K1.Subkind K or disjoint or CaptureKind C K
--         -- Use singleton_proj_disj + sub to get CaptureKind (C.proj K1) K
--         right; left; exists K2;
--       case inr hk2 => right; right; apply sub hsk hk2
--   case empty =>
--     unfold CaptureSet.proj at heq; split at heq <;> simp at heq
--     right; right; apply empty
--   case singleton_proj_kind =>
--     unfold CaptureSet.proj at heq; split at heq <;> simp at heq
--     have ⟨_, _⟩ := heq; subst_vars;
--     left; apply Kind.Subkind.rfl
--   case singleton_proj hk ih =>
--     unfold CaptureSet.proj at heq; split at heq <;> simp at heq
--     have ⟨_, _⟩ := heq; subst_vars;
--     right; right; assumption
--   case singleton_proj_disj hk hd ih =>
--     unfold CaptureSet.proj at heq; split at heq <;> simp at heq
--     have ⟨_, _⟩ := heq; subst_vars;
--     -- hk : CaptureKind Γ (.singleton s) K1', hd : K1'.Disjoint K1
--     -- Need K1.Disjoint K2 and CaptureKind Γ (.singleton s) K2, use K1' as K2
--     right; left; exact ⟨_, hd.symm, hk⟩
--   case union ha hb iha ihb =>
--     unfold CaptureSet.proj at heq; split at heq <;> simp at heq
--     have ⟨_, _⟩ := heq; subst_vars;
--     cases iha $ .refl _
--     case inl hsub => left; assumption
--     case inr h1 =>
--       cases ihb $ .refl _
--       case inl hsub => left; assumption
--       case inr h2 =>
--         cases h1
--         case inl hd1 =>
--           cases h2
--           case inl hd2 =>
--             right; left
--             obtain ⟨K2a, hda, hka⟩ := hd1
--             obtain ⟨K2b, hdb, hkb⟩ := hd2
--             -- Use absurd_disjoint: K1 disjoint K2a means K1 subkind anything

--           case inr hk2 =>
--             right; left
--             obtain ⟨K2, hd, hk1⟩ := hd1
--             exact ⟨K2, hd, union hk1 (hd.absurd_subkind hk2)⟩
--         case inr hk1 =>
--           cases h2
--           case inl hd2 =>
--             right; left
--             obtain ⟨K2, hd, hk2⟩ := hd2
--             exact ⟨K2, hd, union (hd.absurd_subkind hk1) hk2⟩
--           case inr hk2 => right; right; apply! union

-- theorem CaptureKind.proj_inv (hk : CaptureKind Γ (C.proj K1) K) : K1.Subkind K ∨ (∃ K2, K1.Disjoint K2 ∧ CaptureKind Γ C K2) ∨ CaptureKind Γ C K := by
--   apply hk.proj_inv' $ .refl _

-- theorem CaptureKind.proj_disj (hk : CaptureKind Γ C K1) (hd : K1.Disjoint K2) : CaptureKind Γ (C.proj K2) K3 := by
--   induction C
--   case empty => simp; apply empty
--   case union iha ihb =>
--     simp
--     have ⟨_, _⟩ := hk.union_l_inv
--     apply! union (iha _) (ihb _)
--   case singleton => apply! singleton_proj_disj

-- theorem CaptureKind.widen_var
--   (hk : CaptureKind Γ (.singleton s) K)
--   (hb : Γ.Bound x S^C)
--   (hw : WidenVar x s C C') : CaptureKind Γ C' K := by
--   induction hw generalizing K
--   case var => apply! hk.var_inv
--   case proj hw ih =>
--     rw [← CaptureSet.proj_singleton] at hk
--     cases hk.proj_inv
--     case inl hsk => apply sub hsk; apply proj_kind
--     case inr hs =>
--       cases hs
--       case inl hd =>
--         obtain ⟨K2, hd, hk2⟩ := hd
--         -- hd : K'.Disjoint K2, hk2 : CaptureKind Γ (.singleton s) K2
--         -- ih gives us CaptureKind Γ C K2, then proj_disj gives us CaptureKind Γ (C.proj K') K
--         exact proj_disj (ih hk2 hb) hd.symm
--       case inr hk' => apply proj; apply! ih

-- theorem CaptureKind.cbound_inv' (hk : CaptureKind Γ D K) (heq : D = {c=c}) (hb : Γ.CBound c (.bound (.upper C))) : CaptureKind Γ C K := by
--   induction hk <;> (subst_vars; try simp_all)
--   case cvar hb1 => cases Context.cbound_injective hb hb1
--   case cbound hb1 _ _ =>
--     cases Context.cbound_injective hb hb1
--     assumption
--   case cinstr hb1 _ _ => cases Context.cbound_injective hb hb1
--   case sub hsk _ ih => apply! sub

-- theorem CaptureKind.cbound_inv (hk : CaptureKind Γ {c=c} K) (hb : Γ.CBound c (.bound (.upper C))) : CaptureKind Γ C K := by apply! hk.cbound_inv' (.refl _)

-- theorem CaptureKind.cinstr_inv' (hk : CaptureKind Γ D K) (heq : D = {c=c}) (hb : Γ.CBound c (.inst C)) : CaptureKind Γ C K := by
--   induction hk <;> (subst_vars; try simp_all)
--   case cvar hb1 => cases Context.cbound_injective hb hb1
--   case cbound hb1 _ _ => cases Context.cbound_injective hb hb1
--   case cinstr hb1 _ _ =>
--     cases Context.cbound_injective hb hb1
--     assumption
--   case sub hsk _ ih => apply! sub

-- theorem CaptureKind.cinstr_inv (hk : CaptureKind Γ {c=c} K) (hb : Γ.CBound c (.inst C)) : CaptureKind Γ C K := by apply! hk.cinstr_inv' (.refl _)

-- theorem CaptureKind.widen_cbound
--   (hk : CaptureKind Γ (.singleton s) K)
--   (hb : Γ.CBound c (.bound (.upper C)))
--   (hw : WidenCVar c s C C') : CaptureKind Γ C' K := by
--   induction hw generalizing K
--   case var => apply! hk.cbound_inv
--   case proj hw ih =>
--     rw [← CaptureSet.proj_singleton] at hk
--     cases hk.proj_inv
--     case inl hsk => apply sub hsk; apply proj_kind
--     case inr hs =>
--       cases hs
--       case inl hd =>
--         obtain ⟨K2, hd, hk2⟩ := hd
--         exact proj_disj (ih hk2 hb) hd.symm
--       case inr hk' => apply proj; apply! ih

-- theorem CaptureKind.widen_cinstr
--   (hk : CaptureKind Γ (.singleton s) K)
--   (hb : Γ.CBound c (.inst C))
--   (hw : WidenCVar c s C C') : CaptureKind Γ C' K := by
--   induction hw generalizing K
--   case var => apply! hk.cinstr_inv
--   case proj hw ih =>
--     rw [← CaptureSet.proj_singleton] at hk
--     cases hk.proj_inv
--     case inl hsk => apply sub hsk; apply proj_kind
--     case inr hs =>
--       cases hs
--       case inl hd =>
--         obtain ⟨K2, hd, hk2⟩ := hd
--         exact proj_disj (ih hk2 hb) hd.symm
--       case inr hk' => apply proj; apply! ih

-- theorem CaptureKind.lbound_inv' (hk : CaptureKind Γ D K) (heq : D = {x=x}) (hb : Γ.LBound x c S) : Kind.Subkind (.classifier c) K := by
--   induction hk <;> (subst_vars; try simp_all)
--   case var hb1 _ _ => cases Context.bound_lbound_absurd hb1 hb
--   case label hb1 =>
--     have ⟨heq, _⟩ := Context.lbound_inj hb hb1
--     subst_vars
--     apply Kind.Subkind.rfl
--   case sub hsk _ ih => apply ih.trans hsk

-- theorem CaptureKind.lbound_inv (hk : CaptureKind Γ {x=x} K) (hb : Γ.LBound x c S) : Kind.Subkind (.classifier c) K := by apply! hk.lbound_inv' (.refl _)

-- inductive IsAbsurdLabel : Context n m k -> Singleton n k -> Fin n -> Prop where
--   | with_c : Γ.LBound x c S -> K.Disjoint (.classifier c) -> s.IsVarWith x K -> IsAbsurdLabel Γ s x
--   | with_self : Γ.LBound x c S -> K1.Disjoint K2 -> s.IsVarWith x K1 -> IsAbsurdLabel Γ (.proj s K2) x
--   | proj : IsAbsurdLabel Γ s x -> IsAbsurdLabel Γ (s.proj K) x

-- theorem CaptureKind.widen_lbound (hk : CaptureKind Γ (.singleton s) K) (hb : Γ.LBound x c S) (hi : s.IsVar x) : (Kind.classifier c).Subkind K ∨ IsAbsurdLabel Γ s x ∨ ∃ K1, K1.Subkind K ∧ s.IsVarWith x K1 := by
--   induction hi generalizing K
--   case var =>
--     left
--     exact hk.lbound_inv hb
--   case proj s K' hi ih =>
--     rw [← CaptureSet.proj_singleton] at hk
--     cases hk.proj_inv
--     case inl hsk =>
--       right
--       exact ⟨K', hsk, .here hi⟩
--     case inr hs =>
--       cases hs
--       case inl hd =>
--         -- K'.Disjoint K2 and CaptureKind Γ (.singleton s) K2
--         -- This is an absurd projection case - K' projects something of disjoint kind K2
--         obtain ⟨K2, hd, hk2⟩ := hd
--         -- hk2 : CaptureKind Γ (.singleton s) K2, hd : K'.Disjoint K2
--         -- Since singleton_proj_disj gives any kind K, we know the original hk : CaptureKind Γ ((singleton s).proj K') K
--         -- was constructed with an arbitrary K. We return right with K' as the witness.
--         -- K'.Subkind K follows from the fact that the disjoint projection has any kind.
--         -- We can use singleton_proj_disj hk2 hd.symm to reconstruct a CaptureKind with our target kind,
--         -- and then show K'.Subkind K via proj_kind + sub.
--         -- Actually, we can just show K' is the projection that witnesses IsVarWith
--         right
--         -- We need K'.Subkind K. Since hk came from singleton_proj_disj, the overall kind K is arbitrary.
--         -- But we don't have direct access to that. Let's use proj_kind which gives CaptureKind for K' kind.
--         -- From hk : CaptureKind Γ ((singleton s).proj K') K, by cases on construction...
--         -- Actually the simplest: use singleton_proj_disj + sub to derive K'.Subkind K is not directly available.
--         -- Let's try: we know the result has kind K and there's a projection to K', so K'.Subkind K.
--         -- Wait - we're in the case where proj_inv returned the disjoint case, not the subkind case.
--         -- So we DON'T have K'.Subkind K directly from proj_inv.
--         -- But we can construct it: from singleton_proj_disj we get CaptureKind for any kind,
--         -- and from singleton_proj_kind we get CaptureKind Γ (singleton (s.proj K')) K'.
--         -- Combining with sub we'd need K'.Subkind K which is what we want to prove...
--         -- This is circular. Let me try a different approach: return that K' is absurd.
--         -- If K' is disjoint from K2 and K2 has a real classifier, then K' must be absurd.
--         -- Actually no, that's not right either.
--         -- Let me just return K'.Subkind K using Kind.Subkind.rfl won't work since K' ≠ K in general.
--         -- The real answer: in the absurd disjoint case, the projection has ANY kind including K.
--         -- So we should be able to show K' ≤ K. But how?
--         -- From hk we know the proj has kind K. proj_kind says proj has kind K'.
--         -- So by transitivity if we had proj_kind + sub (K' to K), we'd have the proof.
--         -- But we need that sub evidence... which comes from the fact that hk has kind K.
--         -- This is exactly what we'd get if proj_inv returned K'.Subkind K in the first case!
--         -- The issue is proj_inv returns the disjoint case separately.
--         -- Let me use a workaround: we can show K' is subkind of K using the actual hk.
--         -- hk : CaptureKind Γ ((singleton s).proj K') K
--         -- singleton_proj_kind : CaptureKind Γ ((singleton s).proj K') K'
--         -- If we had K' ≠ K with CaptureKind for both, that's fine - both can hold.
--         -- But we need to PROVE K'.Subkind K...
--         -- Actually, let's use CaptureKind.sub backwards: if we have CaptureKind C K' and CaptureKind C K,
--         -- and the only way to go from K' to K is via sub, then we'd need the subkind.
--         -- But that's also not directly provable.
--         --
--         -- SOLUTION: The disjoint case in proj_inv should actually imply K'.Subkind K
--         -- because the only way to get kind K from (singleton (s.proj K')) when the inner has
--         -- disjoint kind K2 is via singleton_proj_disj which gives any K,
--         -- but then sub can lift K' to K.
--         -- The cleanest fix is to change proj_inv to include K'.Subkind K in the disjoint case.
--         -- For now, let me use Kind.Subkind.rfl and see if K' = K in our context (it should be when proj_inv returns case 2)
--         -- Actually no, we're stuck. Let me add a helper or change proj_inv's return type.
--         sorry
--       case inr hk' =>
--         cases ih hk' hb with
--         | inl hsub => left; exact hsub
--         | inr h =>
--           right
--           obtain ⟨K1, hsk1, hvw⟩ := h
--           exact ⟨K1, hsk1, .there hvw⟩





end Capless
