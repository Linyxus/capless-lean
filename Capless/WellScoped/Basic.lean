import Capless.Store
import Capless.Subcapturing
import Capless.Inversion.Context
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

theorem WellScoped.subcapt
  (hsc : WellScoped Γ cont C)
  (hs : Γ ⊢ C' <:c C) :
  WellScoped Γ cont C' := by
  induction hs generalizing cont
  case trans => aesop
  case subset => apply WellScoped.subset <;> easy
  case union => apply union <;> aesop
  case var => apply WellScoped.singleton <;> aesop
  case cinstl =>
    cases hsc
    rename_i hb1 _ _ hb2
    have h := Context.cbound_injective hb1 hb2
    cases h
    easy
  case cinstr => apply WellScoped.csingleton <;> aesop

end Capless
