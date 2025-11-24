import Capless.Store
import Capless.Subcapturing
import Capless.Inversion.Context

/-!
# Basic Properties of Well-Scopedness

This file contains basic properties of the well-scopedness relation.
-/

namespace Capless

theorem WellScoped.subset
  (hsc : WellScoped Γ cont C2)
  (hs : C1 ⊆ C2) : WellScoped Γ cont C1 := by
  induction hs
  case empty => apply empty
  case rfl => apply hsc
  case union_l ha hb iha ihb => apply union (iha hsc) (ihb hsc)
  case union_rl ha iha => cases hsc; aesop
  case union_rr ha iha => cases hsc; aesop
  case trans ha hb iha ihb => apply iha $ ihb hsc
  case proj_empty =>
    apply proj .empty .proj_empty
    simp
  case proj_union_l =>
    cases hsc
    rename_i h1 h2 h3
    have ⟨hl, hr⟩ := CaptureSet.Subset.proj_union_l_inv h3
    apply union
    { apply proj h1 hl;  }

  case proj_union_r =>
    cases hsc
    rename_i h1 h2
    apply proj
    apply union h1 h2
    apply CaptureSet.Subset.proj_union_r
  case proj_proj =>
    cases hsc
    rename_i h1 h2
    apply proj h1
    apply CaptureSet.Subset.trans .proj_proj h2
  case proj_l =>
    apply proj hsc .proj_l
  case proj ha ih =>
    cases hsc
    case proj =>
      rename_i h1 ih2
      apply proj h1
      apply CaptureSet.Subset.trans _ ih2
      apply! CaptureSet.Subset.proj
    case label_disj =>
      apply proj
      apply! label_disj
      apply! CaptureSet.Subset.proj



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
