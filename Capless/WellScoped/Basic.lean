import Capless.Store
import Capless.Subcapturing
import Capless.Inversion.Context

/-!
# Basic Properties of Well-Scopedness

This file contains basic properties of the well-scopedness relation.
-/

namespace Capless

theorem WellScoped.implies_canonical (hsc : WellScoped Γ cont C) : ProjectedSingletonsOnly C := by
  induction hsc
  case empty => constructor
  case union ha hb iha ihb => apply! ProjectedSingletonsOnly.union
  case singleton => apply ProjectedSingletonsOnly.singleton; constructor
  case csingleton => apply ProjectedSingletonsOnly.singleton; constructor
  case cbound => apply ProjectedSingletonsOnly.singleton; constructor
  case ckind => apply ProjectedSingletonsOnly.singleton; constructor
  case proj_singleton => apply! ProjectedSingletonsOnly.singleton
  case label => apply ProjectedSingletonsOnly.singleton; constructor
  case label_disj _ _ hsw => apply ProjectedSingletonsOnly.singleton; apply hsw.erase

theorem WellScoped.push_proj (hsc : WellScoped Γ cont C) : WellScoped Γ cont (C.push_proj K) := by
  induction hsc generalizing K <;> try simp_all
  case empty => apply empty
  case union iha ihb => apply union iha ihb
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
    rw [← CaptureSet.push_proj_singleton_eq hp]
    apply! ProjectedSingleton.proj
  case label hb hs =>
    apply proj_singleton
    apply label hb hs
    apply ProjectedSingleton.proj .var
  case label_disj hb hd hp  =>
    apply label_disj hb hd
    rw [CaptureSet.push_proj_singleton_eq $ hp.erase]
    apply! ProjectedSingletonWith.there

theorem WellScoped.push_proj_sub {C : CaptureSet n k} (hsc : WellScoped Γ cont (C.push_proj K2)) (hsk : K1.Subkind K2) : WellScoped Γ cont (C.push_proj K1) := by
  --  hsc.implies_canonical

theorem WellScoped.has_singleton
  (hsc : WellScoped Γ cont C2)
  (hh : HasSingleton C C2) :
  WellScoped Γ cont C := by
  induction hsc generalizing C
  case empty => cases hh
  case union ha hb iha ihb =>
    cases hh
    case union_l hh => apply! iha
    case union_r hh => apply! ihb
  case singleton =>
    cases hh
    apply! singleton
  case csingleton =>
    cases hh
    apply! csingleton
  case cbound =>
    cases hh
    apply! cbound
  case ckind =>
    cases hh
    apply! ckind
  case proj_singleton hsc hp ih =>
    have hh1 := CaptureSet.projected_singleton_unique_singleton hp hh
    subst_vars
    apply! proj_singleton
  case label hb hl =>
    cases hh
    apply! label
  case label_disj hb hd hp =>
    have hh1 := CaptureSet.projected_singleton_unique_singleton hp.erase hh
    subst_vars
    apply! label_disj


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
  case singleton hp =>
    have hp2 := CaptureSet.subset_has_singleton hs (CaptureSet.projected_singleton_has_singleton hp)
    apply has_singleton hsc hp2

theorem WellScoped.subset {C1 C2 : CaptureSet n k}
  (hsc : WellScoped Γ cont C2.canonicalize)
  (hs : C1 ⊆ C2) : WellScoped Γ cont C1.canonicalize := by
  have h := CaptureSet.Subset.canonicalize hs
  apply subset' hsc h
  repeat apply CaptureSet.canonicalize_is_projected_singletons_only

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

theorem WellScoped.subcapt
  (hsc : WellScoped Γ cont C.canonicalize)
  (hs : Γ ⊢ C' <:c C) :
  WellScoped Γ cont C'.canonicalize :=
  match hs with
  | .trans ha hb => .subcapt (.subcapt hsc hb) ha
  | .subset hs => .subset hsc hs
  | .union ha hb => .union (.subcapt hsc ha) (.subcapt hsc hb)
  | .var hb => .singleton hb hsc
  | .cinstl hb1 => by
    simp at hsc
    cases hsc <;> (rename_i hb2; try cases Context.cbound_injective hb1 hb2)
    assumption
    cases hb2
  | .cinstr hb => .csingleton hb hsc
  | .cbound hb => .cbound hb hsc
  | .proj h1 => by sorry
  | .proj_sub hs => by
    simp_all
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
