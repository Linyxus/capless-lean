import Capless.Store
import Capless.Subcapturing
import Capless.Inversion.Context

/-!
# Basic Properties of Well-Scopedness

This file contains basic properties of the well-scopedness relation.
-/

namespace Capless

theorem WellScoped.subset
  (hsc : WellScoped Γ cont C)
  (hs : C' ⊆ C) :
  WellScoped Γ cont C' := by
  induction hs
  case empty => apply empty
  case rfl => easy
  case union_l => apply WellScoped.union <;> aesop
  case union_rl =>
    cases hsc
    aesop
  case union_rr =>
    cases hsc
    aesop
  case proj_empty =>
    constructor
  case empty_proj =>
    constructor
    constructor
  case proj_union =>
    constructor
    cases hsc
    rename_i ha hb
    constructor
    cases ha; assumption
    cases hb; assumption
  case union_proj =>
    constructor <;> constructor
    cases hsc
    rename_i h1
    cases h1; assumption
    cases hsc
    rename_i h1
    cases h1; assumption
  case proj_proj =>
    cases hsc
    rename_i h1
    cases h1
    constructor
    constructor
    assumption

theorem WellScoped.cons
  (hsc : WellScoped Γ cont C) :
  WellScoped Γ (Cont.cons u cont) C := by
  induction hsc
  case empty => apply empty
  case union ih1 ih2 => apply union <;> aesop
  case singleton ih => apply singleton <;> aesop
  case csingleton ih => apply csingleton <;> aesop
  case cbound ih => apply cbound <;> aesop
  case ckind ih => apply ckind <;> aesop
  case label =>
    apply label
    easy
    constructor; easy
  case proj =>
    constructor; easy

theorem WellScoped.conse
  (hsc : WellScoped Γ cont C) :
  WellScoped Γ (Cont.conse u cont) C := by
  induction hsc
  case empty => apply empty
  case union ih1 ih2 => apply union <;> aesop
  case singleton ih => apply singleton <;> aesop
  case csingleton ih => apply csingleton <;> aesop
  case cbound ih => apply cbound <;> aesop
  case ckind ih => apply ckind <;> aesop
  case label =>
    apply label
    easy
    constructor; easy
  case proj => constructor; easy

theorem WellScoped.scope
  (hsc : WellScoped Γ cont C) :
  WellScoped Γ (Cont.scope x cont) C := by
  induction hsc
  case empty => apply empty
  case union ih1 ih2 => apply union <;> aesop
  case singleton ih => apply singleton <;> aesop
  case csingleton ih => apply csingleton <;> aesop
  case cbound ih => apply cbound <;> aesop
  case ckind ih => apply ckind <;> aesop
  case label =>
    apply label
    easy
    constructor; easy
  case proj => constructor; easy

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
    cases hsc
    case csingleton =>
      rename_i hb2
      have h := Context.cbound_injective hb1 hb2
      cases h
      rename_i h
      exact h
    case cbound =>
      rename_i hb2
      have h := Context.cbound_injective hb1 hb2
      cases h
    case ckind =>
      rename_i hb2
      have h := Context.cbound_injective hb1 hb2
      cases h
  | .cinstr hb => .csingleton hb hsc
  | .cbound hb => .cbound hb hsc
  | .proj h1 => by
    constructor
    cases hsc
    apply WellScoped.subcapt _ h1; assumption
  | .proj_sub hs => by
    constructor
    cases hsc
    assumption
  | .proj_l => by constructor; assumption
  | .proj_r hs => by
    cases hsc
    assumption
  | .proj_disj _ _ => _

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
