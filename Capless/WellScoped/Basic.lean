import Capless.Store
import Capless.Subcapturing
import Capless.Inversion.Context

/-!
# Basic Properties of Well-Scopedness

This file contains basic properties of the well-scopedness relation.
-/

namespace Capless

theorem WellScoped.push_proj (hsc : WellScoped Γ cont C) : WellScoped Γ cont (C.push_proj K) := by
  induction hsc <;> try simp_all
  case empty => apply empty
  case union iha ihb => apply! union
  case singleton hb ha ih =>
    apply proj_singleton
    apply singleton hb ha
    apply ProjectedSingleton.proj .var
  case csingleton hb ha ih =>
    apply proj_singleton
    apply csingleton hb ha
    apply ProjectedSingleton.proj .cvar
  case cbound hb ha ih =>
    apply proj_singleton
    apply cbound hb ha
    apply ProjectedSingleton.proj .cvar
  case ckind hb =>
    apply proj_singleton
    apply ckind hb
    apply ProjectedSingleton.proj .cvar
  case proj_singleton h1 hp ih =>
    apply proj_singleton h1
    rw [CaptureSet.push_proj_singleton_eq hp]
    apply! ProjectedSingleton.proj
  case label hb hs =>
    apply proj_singleton
    apply label hb hs
    apply ProjectedSingleton.proj .var
  case label_disj hb hd hp  =>
    apply label_disj hb hd
    rw [CaptureSet.push_proj_singleton_eq $ hp.erase]
    apply! ProjectedSingletonWith.there

-- theorem WellScoped.singleton_inv (hsc : WellScoped Γ cont C') (hs : C ⊆ C') (hp : ProjectedSingleton S C) : WellScoped Γ cont C := by
--   induction hsc
--   case empty =>

theorem WellScoped.subset' (hsc : WellScoped Γ cont C2)
  (hs : C1 ⊆ C2)
  (hp1 : ProjectedSingletonsOnly C1)
  (hp2 : ProjectedSingletonsOnly C2) : WellScoped Γ cont C1 := by
  induction hp1
  case empty => apply empty
  case union ha hb iha ihb =>
    have ⟨_, _⟩ := CaptureSet.Subset.union_l_inv hs
    apply union
    apply! iha
    apply! ihb
  case singleton =>
    induction hp2
    case empty =>
      have h1 := CaptureSet.Subset.empty_only hs .base
      induction h1
      case base => apply empty
      case union h1 h2 ih1 ih2 => cases ih2
      case proj ih h1 =>
        cases h1



theorem WellScoped.subset {C1 C2 : CaptureSet n k}
  (hsc : WellScoped Γ cont C2.canonicalize)
  (hs : C1 ⊆ C2) : WellScoped Γ cont C1.canonicalize := by
  induction hs <;> simp_all
  case empty => apply empty
  case union_l ha hb iha ihb => apply! union
  case union_rl ha iha =>
    cases hsc
    case proj_singleton hp => cases hp
    case label_disj hp => cases hp
    case union ha hb =>
      apply! iha
  case union_rr ha iha =>
    cases hsc
    case proj_singleton hp => cases hp
    case label_disj hp => cases hp
    case union ha hb => apply! iha
  case proj_l =>
    apply hsc.push_proj
  case proj C D K hs ih =>
    -- induction D <;> simp_all
    -- case empty =>



  -- case trans ha hb iha ihb => apply iha $ ihb hsc
  -- case proj_empty =>
  --   apply proj .empty .proj_empty
  --   simp
  -- case proj_union_l =>
  --   cases hsc
  --   rename_i h1 h2 h3
  --   have ⟨hl, hr⟩ := CaptureSet.Subset.proj_union_l_inv h3
  --   apply union
  --   { apply proj h1 hl;  }

  -- case proj_union_r =>
  --   cases hsc
  --   rename_i h1 h2
  --   apply proj
  --   apply union h1 h2
  --   apply CaptureSet.Subset.proj_union_r
  -- case proj_proj =>
  --   cases hsc
  --   rename_i h1 h2
  --   apply proj h1
  --   apply CaptureSet.Subset.trans .proj_proj h2
  -- case proj_l =>
  --   apply proj hsc .proj_l
  -- case proj ha ih =>
  --   cases hsc
  --   case proj =>
  --     rename_i h1 ih2
  --     apply proj h1
  --     apply CaptureSet.Subset.trans _ ih2
  --     apply! CaptureSet.Subset.proj
  --   case label_disj =>
  --     apply proj
  --     apply! label_disj
  --     apply! CaptureSet.Subset.proj



theorem WellScoped.cons
  (hsc : WellScoped Γ cont C) :
  WellScoped Γ (Cont.cons u cont) C := by
  induction hsc
  case empty => apply empty
  case union => apply union <;> aesop
  case proj => apply proj <;> aesop
  case singleton ih => apply singleton <;> aesop
  case csingleton ih => apply csingleton <;> aesop
  case cbound ih => apply cbound <;> aesop
  case ckind ih => apply ckind <;> aesop
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
  case proj => apply proj <;> aesop
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
  case proj => apply proj <;> aesop
  case singleton ih => apply singleton <;> aesop
  case csingleton ih => apply csingleton <;> aesop
  case cbound ih => apply cbound <;> aesop
  case ckind ih => apply ckind <;> aesop
  case label =>
    apply label
    easy
    constructor; easy
  case label_disj => apply! label_disj

theorem WellScoped.subcapt
  (hsc : WellScoped Γ cont C)
  (hs : Γ ⊢ C' <:c C) :
  WellScoped Γ cont C' :=
  match hs with
  | .trans ha hb => .subcapt (.subcapt hsc hb) ha
  | .subset hs => .subset hsc hs
  | .union ha hb => .union (.subcapt hsc ha) (.subcapt hsc hb)
  | .var hb => .singleton hb hsc
  | .cinstl hb1 => by
    cases hsc <;> (rename_i hb2; cases Context.cbound_injective hb1 hb2)
    assumption
  | .cinstr hb => .csingleton hb hsc
  | .cbound hb => .cbound hb hsc
  | .proj h1 => by
    cases hsc
    rename_i s D2 K D3 hsc hs
  | .proj_sub hs => by
    constructor
    cases hsc
    assumption
  | .proj_l => by constructor; assumption
  | .proj_r hs => by
    cases hsc
    assumption
  | .proj_disj hd hk => by sorry


theorem WellScoped.var_inv
  (hsc : WellScoped Γ cont {x=x})
  (hbx : Γ.Bound x (S^C)) :
  WellScoped Γ cont C := by
  cases hsc
  case singleton =>
    rename_i hbx'
    have h := Context.bound_injective hbx hbx'
    cases h
    trivial
  case label =>
    exfalso
    apply Context.bound_lbound_absurd <;> easy

theorem WellScoped.label_inv
  (hsc : WellScoped Γ cont {x=x})
  (hbl : Γ.LBound x S) :
  ∃ tail, cont.HasLabel x tail := by
  cases hsc
  case singleton =>
    exfalso
    apply Context.bound_lbound_absurd <;> easy
  case label => aesop

end Capless
