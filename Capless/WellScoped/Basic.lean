import Capless.Store
import Capless.Subcapturing
import Capless.Inversion.Context

/-!
# Basic Properties of Well-Scopedness

This file contains basic properties of the well-scopedness relation.
-/

namespace Capless

theorem WellScoped.proj (hsc : WellScoped Γ cont C) : WellScoped Γ cont (C.proj K) := by
  induction hsc generalizing K <;> try simp_all
  case empty => apply empty
  case union iha ihb => apply union iha ihb
  case singleton hb ha ih =>
    apply proj_singleton
    apply singleton hb ha
    apply HasSingleton.proj .var
  case csingleton hb ha ih =>
    apply proj_singleton
    apply csingleton hb ha
    apply HasSingleton.proj .cvar
  case cbound hb ha ih =>
    apply proj_singleton
    apply cbound hb ha
    apply HasSingleton.proj .cvar
  case ckind hb =>
    apply proj_singleton
    apply ckind hb
    apply HasSingleton.proj .cvar
  case proj_singleton h1 hp ih =>
    apply proj_singleton h1
    apply! HasSingleton.proj
  case label hb hs =>
    apply proj_singleton
    apply label hb hs
    apply HasSingleton.proj .var
  case label_disj hb hd hp  =>
    apply label_disj hb hd
    apply! HasSingletonProj.there

theorem WellScoped.has_singleton
  (hsc : WellScoped Γ cont (.singleton C2))
  (hh : HasSingleton C C2) :
  WellScoped Γ cont (.singleton C) := by
  induction hh
  case var => assumption
  case cvar => assumption
  case proj =>
    apply proj_singleton
    apply hsc
    apply! HasSingleton.proj


-- theorem WellScoped.subset' (hsc : WellScoped Γ cont C2)
--   (hs : C1 ⊆ C2)
--   (hp1 : ProjectedSingletonsOnly C1)
--   (hp2 : ProjectedSingletonsOnly C2) : WellScoped Γ cont C1 := by
--   induction hp1
--   case empty => apply empty
--   case union ha hb iha ihb =>
--     have ⟨_, _⟩ := CaptureSet.Subset.union_l_inv hs
--     apply union
--     apply! iha
--     apply! ihb
--   case singleton hp =>
--     have hp2 := CaptureSet.subset_has_singleton hs (CaptureSet.projected_singleton_has_singleton hp)
--     apply has_singleton hsc hp2

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
  case proj_singleton ha hp ih =>
    apply proj_singleton <;> aesop
  case label =>
    apply label
    easy
    constructor; easy
  case label_disj hb hd =>
    apply! label_disj

theorem WellScoped.conse
  (hsc : WellScoped Γ cont C) :
  WellScoped Γ (Cont.conse u cont) C := by
  induction hsc
  case empty => apply empty
  case union => apply union <;> aesop
  case proj_singleton ha hp ih =>
    apply proj_singleton <;> aesop
  case singleton ih => apply singleton <;> aesop
  case csingleton ih => apply csingleton <;> aesop
  case cbound ih => apply cbound <;> aesop
  case ckind ih => apply ckind <;> aesop
  case label =>
    apply label
    easy
    constructor; easy
  case label_disj => apply! label_disj

theorem WellScoped.scope
  (hsc : WellScoped Γ cont C) :
  WellScoped Γ (Cont.scope x cont) C := by
  induction hsc
  case empty => apply empty
  case union => apply union <;> aesop
  case proj_singleton ha hp ih =>
    apply proj_singleton <;> aesop
  case singleton ih => apply singleton <;> aesop
  case csingleton ih => apply csingleton <;> aesop
  case cbound ih => apply cbound <;> aesop
  case ckind ih => apply ckind <;> aesop
  case label =>
    apply label
    easy
    constructor; easy
  case label_disj => apply! label_disj

theorem WellScoped.subkind {C : CaptureSet n k}
  (hsc : WellScoped Γ cont (C.proj K2))
  (hs : K1.Subkind K2)
  : WellScoped Γ cont (C.proj K1) := by
  generalize h : C.proj K2 = D at hsc
  cases hsc
  case empty =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    simp
    constructor
  case union ha hb =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply union (ha.subkind hs) (hb.subkind hs)
  case singleton =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
  case csingleton =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
  case cbound =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
  case ckind =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
  case proj_singleton hh hsc =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    have ⟨_, _⟩ := h; subst_vars; simp_all
    apply proj_singleton hsc
    cases hh
    apply! HasSingleton.proj
  case label =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
  case label_disj hb hd hp =>
    unfold CaptureSet.proj at h; split at h <;> simp at h
    subst_vars; simp_all
    -- apply label_disj hb hd
    cases hp
    case here hp =>
      apply! label_disj hb (hd.refine_by_subkind _) $ .here _
    case there hp =>
      apply! label_disj hb hd $ .there _

-- theorem WellScoped.capture_kind (hk : CaptureKind Γ C K) : WellScoped Γ cont C := by
--   induction hk
--   case var => apply! singleton
--   case cvar => apply! ckind
--   case cbound => apply! cbound
--   case cinstr => apply! csingleton
--   case sub => assumption
--   case empty => apply! empty
--   case singleton_proj_kind

theorem WellScoped.capture_kind (hsc : WellScoped Γ cont (C.proj K)) (hk : Γ ⊢ C :k K) : WellScoped Γ cont C := by
  induction hk
  case var hb hk ih =>
    cases hsc
    case proj_singleton hsc hs =>
      cases hs
      rename_i hs
      cases hs
      assumption
    case label_disj hb1 hd hsp =>
      cases hsp
      case here hs =>
        cases hs
        cases Context.bound_lbound_absurd hb hb1
      case there hsp => cases hsp
  case cvar hb => apply! ckind
  case cbound hb hk ih =>
    cases hsc
    case proj_singleton hsc hs =>
      cases hs
      rename_i hs
      cases hs
      assumption
    case label_disj hsp =>
      cases hsp
      case here hs _ => cases hs
      case there hsp => cases hsp
  case cinstr hb hk ih =>
    cases hsc
    case proj_singleton hsc hs =>
      cases hs
      rename_i hs
      cases hs
      assumption
    case label_disj hsp =>
      cases hsp
      case here hs _ => cases hs
      case there hsp => cases hsp
  case sub hsk hk ih =>
    apply! ih $ hsc.subkind _
  case empty => apply! empty
  case singleton_proj_kind =>
    cases hsc
    case proj_singleton hsc hs =>
      cases hs
      rename_i hs
      cases hs
      apply! proj_singleton hsc $ .proj _
    case label_disj hb hd hsp =>
      cases hsp
      case here hs =>
        cases hs
        apply! label_disj hb hd $ .here _
      case there hsp =>
        apply! label_disj
  case singleton_proj hk ih =>
    cases hsc
    case proj_singleton hsc hs =>
      cases hs
      apply! proj_singleton hsc
    case label_disj hb hd hsp =>
      cases hsp
      case here hs =>
        cases hs
        rename_i hs
        have h := label_disj hb hd (.here hs) (cont:=cont)
        have h1 := ih h
        apply h1.proj
      case there hsp => apply! label_disj
  -- case singleton_proj_disj hk hd ih =>
  --   cases hsc
  --   case proj_singleton hsc hs =>
  --     cases hs
  --     apply! proj_singleton
  --   case label_disj hb hd hsp =>
  --     cases hsp
  --     case here hs =>
  case union ha hb iha ihb =>
    simp at hsc
    cases hsc
    apply! union (iha _) (ihb _)

theorem WellScoped.subcapt
  (hsc : WellScoped Γ cont C)
  (hs : Γ ⊢ C' <:c C) :
  WellScoped Γ cont C' := by
  induction hs
  case trans ih1 ih2 => exact ih1 (ih2 hsc)
  case subset hs => exact hsc.subset hs
  case union ih1 ih2 => exact .union (ih1 hsc) (ih2 hsc)
  case var hb => exact .singleton hb hsc
  case cinstl hb1 =>
    cases hsc
    case csingleton hb =>
      have h := Context.cbound_injective hb1 hb; injections; subst_vars
      assumption
    case cbound hb => cases Context.cbound_injective hb1 hb
    case ckind hb => cases Context.cbound_injective hb1 hb
    case label_disj hsp => cases hsp
  case cinstr hb => exact .csingleton hb hsc
  case cbound hb => exact .cbound hb hsc
  case singleton_proj_sub hs =>
    rename_i s K1 K2
    have h : (CaptureSet.singleton (s.proj K2)) = (CaptureSet.singleton s).proj K2 := by simp
    rw [h] at hsc
    exact hsc.subkind hs
  case singleton_proj_l => exact hsc.proj
  case proj_r C D K hs hk ih =>
    cases hk
    case cvar => apply! ckind
    case var hb hk =>

      sorry
    case cbound => sorry
    case cinstr => sorry
    case sub => sorry
    case empty => sorry
    case singleton_proj_kind => sorry
    case singleton_proj => sorry
    -- case singleton_proj_disj => sorry
    case union => sorry
  case singleton_proj_disj hd hk => sorry
-- termination_by?

-- theorem WellScoped.subkind

-- theorem WellScoped.var_inv
--   (hsc : WellScoped Γ cont {x=x})
--   (hbx : Γ.Bound x (S^C)) :
--   WellScoped Γ cont C := by
--   cases hsc
--   case singleton =>
--     rename_i hbx'
--     have h := Context.bound_injective hbx hbx'
--     cases h
--     trivial
--   case label =>
--     exfalso
--     apply Context.bound_lbound_absurd <;> easy

-- theorem WellScoped.label_inv
--   (hsc : WellScoped Γ cont {x=x})
--   (hbl : Γ.LBound x S) :
--   ∃ tail, cont.HasLabel x tail := by
--   cases hsc
--   case singleton =>
--     exfalso
--     apply Context.bound_lbound_absurd <;> easy
--   case label => aesop

end Capless
