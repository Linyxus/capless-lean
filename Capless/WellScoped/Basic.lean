import Capless.Store
import Capless.Subcapturing
import Capless.Inversion.Context

/-!
# Basic Properties of Well-Scopedness

This file contains basic properties of the well-scopedness relation.
-/

namespace Capless

theorem WellScoped.proj (hsc : WellScoped Γ cont C) : WellScoped Γ cont (C.proj K) := by
  induction hsc generalizing K <;> simp
  case empty => apply empty
  case union iha ihb => apply union iha ihb
  case singleton hb hw hsc ih => apply singleton hb hw.proj ih
  case csingleton hb hw hsc ih => apply csingleton hb hw.proj ih
  case cbound hb hw hsc ih => apply cbound hb hw.proj ih
  case ckind hb hw => apply ckind hb hw.proj
  case label hb hl hw => apply label hb hl hw.proj
  case label_disj hb hd hw => apply label_disj hb hd hw.there

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
  case label hb hl hw =>
    apply label hb
    constructor; assumption
    apply hw
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
  case label hb hl hw =>
    apply label hb
    constructor; assumption
    apply hw
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
  case label hb hl hw =>
    apply label hb
    constructor; assumption
    apply hw
  case label_disj => apply! label_disj

theorem WellScoped.subkind' {C D : CaptureSet n k}
  (hsc : WellScoped Γ cont D)
  (heq : D = C.proj K2)
  (hs : K1.Subkind K2)
  : WellScoped Γ cont (C.proj K1) := by
  induction hsc <;> (unfold CaptureSet.proj at heq; split at heq <;> simp at heq; simp)
  { apply empty }
  { have ⟨_, _⟩ := heq; subst_vars; simp_all
    rename_i ih1 _ ih2
    apply union (ih1 _) (ih2 _) <;> rfl }
  { subst_vars
    rename_i hw
    cases hw
    rename_i hb _ _ _ hw hsc ih
    apply singleton hb (.proj hw) (ih _)
    rfl }
  { subst_vars
    rename_i hw
    cases hw
    rename_i hb _ _ _ hw hsc ih
    apply csingleton hb (.proj hw) (ih _)
    rfl }
  { subst_vars
    rename_i hw
    cases hw
    rename_i hb _ _ _ hw hsc ih
    apply cbound hb (.proj hw) (ih _)
    rfl }
  { subst_vars
    rename_i hw
    apply! ckind _ hw.proj_inv.proj
  }
  { subst_vars
    rename_i hw
    apply! label _ _ hw.proj_inv.proj
  }
  { subst_vars
    rename_i hw
    cases hw
    case here hw => apply! label_disj _ (hw.refine_by_subkind _) (.here _)
    case there hw => apply! label_disj _ _ (.there _)
  }

theorem WellScoped.subkind {C: CaptureSet n k} (hsc : WellScoped Γ cont (C.proj K2)) (hs : K1.Subkind K2) : WellScoped Γ cont (C.proj K1) := by
  apply subkind' hsc _ hs
  rfl

theorem WellScoped.subcapt (hsc : WellScoped Γ cont C2) (hsub : Subcapt Γ C1 C2) : WellScoped Γ cont C1 := by
  induction hsub
  case trans ha hb iha ihb => apply! iha $ ihb _
  case subset hsub => apply! hsc.subset
  case union ha hb iha ihb =>
    apply! union (iha _) (ihb _)
  case var hb => apply! singleton _ .var
  case cinstl hb =>
    cases hsc
    case singleton hv => cases hv
    case csingleton hb1 _ _ _ hv =>
      cases hv
      cases Context.cbound_injective hb1 hb
      assumption
    case cbound hb1 _ _ _ hv =>
      cases hv
      cases Context.cbound_injective hb1 hb
    case ckind hb1 hv =>
      cases hv
      cases Context.cbound_injective hb1 hb
    case label hv => cases hv
    case label_disj hv => cases hv
  case cinstr hb =>
    apply csingleton hb _ _







-- theorem WellScoped.capture_kind (hsc : WellScoped Γ cont (C.proj K)) (hk : Γ ⊢ C :k K) : WellScoped Γ cont C := by
--   induction hk
--   case var hb hk ih =>
--     cases hsc
--     case proj_singleton hsc hs =>
--       cases hs
--       rename_i hs
--       cases hs
--       assumption
--     case label_disj hb1 hd hsp =>
--       cases hsp
--       case here hs =>
--         cases hs
--         cases Context.bound_lbound_absurd hb hb1
--       case there hsp => cases hsp
--   case cvar hb => apply! ckind
--   case cbound hb hk ih =>
--     cases hsc
--     case proj_singleton hsc hs =>
--       cases hs
--       rename_i hs
--       cases hs
--       assumption
--     case label_disj hsp =>
--       cases hsp
--       case here hs _ => cases hs
--       case there hsp => cases hsp
--   case cinstr hb hk ih =>
--     cases hsc
--     case proj_singleton hsc hs =>
--       cases hs
--       rename_i hs
--       cases hs
--       assumption
--     case label_disj hsp =>
--       cases hsp
--       case here hs _ => cases hs
--       case there hsp => cases hsp
--   case sub hsk hk ih =>
--     apply! ih $ hsc.subkind _
--   case empty => apply! empty
--   case singleton_proj_kind =>
--     cases hsc
--     case proj_singleton hsc hs =>
--       cases hs
--       rename_i hs
--       cases hs
--       apply! proj_singleton hsc $ .proj _
--     case label_disj hb hd hsp =>
--       cases hsp
--       case here hs =>
--         cases hs
--         apply! label_disj hb hd $ .here _
--       case there hsp =>
--         apply! label_disj
--   case singleton_proj hk ih =>
--     cases hsc
--     case proj_singleton hsc hs =>
--       cases hs
--       apply! proj_singleton hsc
--     case label_disj hb hd hsp =>
--       cases hsp
--       case here hs =>
--         cases hs
--         rename_i hs
--         have h := label_disj hb hd (.here hs) (cont:=cont)
--         have h1 := ih h
--         apply h1.proj
--       case there hsp => apply! label_disj
--   -- case singleton_proj_disj hk hd ih =>
--   --   cases hsc
--   --   case proj_singleton hsc hs =>
--   --     cases hs
--   --     apply! proj_singleton
--   --   case label_disj hb hd hsp =>
--   --     cases hsp
--   --     case here hs =>
--   case union ha hb iha ihb =>
--     simp at hsc
--     cases hsc
--     apply! union (iha _) (ihb _)

-- theorem WellScoped.subcapt
--   (hsc : WellScoped Γ cont C)
--   (hs : Γ ⊢ C' <:c C) :
--   WellScoped Γ cont C' := by
--   induction hs
--   case trans ih1 ih2 => exact ih1 (ih2 hsc)
--   case subset hs => exact hsc.subset hs
--   case union ih1 ih2 => exact .union (ih1 hsc) (ih2 hsc)
--   case var hb => exact .singleton hb hsc
--   case cinstl hb1 =>
--     cases hsc
--     case csingleton hb =>
--       have h := Context.cbound_injective hb1 hb; injections; subst_vars
--       assumption
--     case cbound hb => cases Context.cbound_injective hb1 hb
--     case ckind hb => cases Context.cbound_injective hb1 hb
--     case label_disj hsp => cases hsp
--   case cinstr hb => exact .csingleton hb hsc
--   case cbound hb => exact .cbound hb hsc
--   case singleton_proj_sub hs =>
--     rename_i s K1 K2
--     have h : (CaptureSet.singleton (s.proj K2)) = (CaptureSet.singleton s).proj K2 := by simp
--     rw [h] at hsc
--     exact hsc.subkind hs
--   case singleton_proj_l => exact hsc.proj
--   case proj_r C D K hs hk ih =>
--     cases hk
--     case cvar => apply! ckind
--     case var hb hk =>

--       sorry
--     case cbound => sorry
--     case cinstr => sorry
--     case sub => sorry
--     case empty => sorry
--     case singleton_proj_kind => sorry
--     case singleton_proj => sorry
--     -- case singleton_proj_disj => sorry
--     case union => sorry
--   case singleton_proj_disj hd hk => sorry
-- -- termination_by?

-- -- theorem WellScoped.subkind

-- -- theorem WellScoped.var_inv
-- --   (hsc : WellScoped Γ cont {x=x})
-- --   (hbx : Γ.Bound x (S^C)) :
-- --   WellScoped Γ cont C := by
-- --   cases hsc
-- --   case singleton =>
-- --     rename_i hbx'
-- --     have h := Context.bound_injective hbx hbx'
-- --     cases h
-- --     trivial
-- --   case label =>
-- --     exfalso
-- --     apply Context.bound_lbound_absurd <;> easy

-- -- theorem WellScoped.label_inv
-- --   (hsc : WellScoped Γ cont {x=x})
-- --   (hbl : Γ.LBound x S) :
-- --   ∃ tail, cont.HasLabel x tail := by
-- --   cases hsc
-- --   case singleton =>
-- --     exfalso
-- --     apply Context.bound_lbound_absurd <;> easy
-- --   case label => aesop

end Capless
