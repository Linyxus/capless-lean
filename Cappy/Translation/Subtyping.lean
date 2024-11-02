import Cappy.Translation.Subcapturing
import Cappy.TypeSystem
import Capless.Subtyping
namespace Cappy

def CType.interp_monotonic.motive_1
  (Γ : Context n m)
  (T1 T2 : CType n m)
  (_ : CSubtyp Γ T1 T2) : Prop :=
  ∀ {k} {Δ : Capless.Context n m k} {ρ} (_ : Context.Interp Γ ⟨Δ, ρ⟩)
    {D1 Q1} (_ : CType.Interp ρ Γ T1 D1 Q1),
  ∃ D2 Q2,
    CType.Interp ρ Γ T2 D2 Q2 ∧
    (Δ ⊢ Q1 <: Q2)

def CType.interp_monotonic.motive_2
  (Γ : Context n m)
  (S1 S2 : SType n m)
  (_ : SSubtyp Γ S1 S2) : Prop :=
  ∀ {k} {Δ : Capless.Context n m k} {ρ} (_ : Context.Interp Γ ⟨Δ, ρ⟩)
    {C D1 Q1} (_ : CType.Interp ρ Γ (S1^C) D1 Q1),
  ∃ D2 Q2,
    CType.Interp ρ Γ (S2^C) D2 Q2 ∧
    (Δ ⊢ Q1 <: Q2)


theorem CType.interp_monotonic
  (hg : Context.Interp Γ ⟨Δ, ρ⟩)
  (hsub : CSubtyp Γ T1 T2)
  (hi : CType.Interp ρ Γ T1 D1 Q1) :
  ∃ D2 Q2,
    CType.Interp ρ Γ T2 D2 Q2 ∧
    (Δ ⊢ Q1 <: Q2) := by
  apply CSubtyp.rec
    (motive_1 := CType.interp_monotonic.motive_1)
    (motive_2 := CType.interp_monotonic.motive_2)
    (t := hsub)
    (D1 := D1)
  all_goals try assumption
  case capt =>
    repeat intro
    sorry
  case top => sorry
  case refl => sorry
  case trans => sorry
  case tvar => sorry
  case boxed => sorry
  case arrow => sorry
  case tarrow => sorry

end Cappy
