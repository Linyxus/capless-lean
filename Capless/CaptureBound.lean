import Capless.CaptureSet
import Capless.Type
import Capless.Subcapturing

namespace Capless

inductive CaptureKind : Context n m k -> CaptureSet n k -> Kind -> Prop where
  | var : Context.Bound Γ x (S^C) -> CaptureKind Γ C K -> CaptureKind Γ {x=x} K
  | label : Context.LBound Γ x S -> CaptureKind Γ {x=x} Kind.control
  | cvar : Context.CBound Γ c (.bound (.kind K)) -> CaptureKind Γ {c=c} K
  | csub : Subcapt Γ C1 C2 -> CaptureKind Γ C2 K -> CaptureKind Γ C1 K -- Should cover all the cinst cases, otherwise we can prove
  | sub : Kind.Subkind K L -> CaptureKind Γ C K -> CaptureKind Γ C L
  | union : CaptureKind Γ C1 K -> CaptureKind Γ C2 K -> CaptureKind Γ (C1 ∪ C2) K
  | empty : CaptureKind Γ .empty K

inductive CaptureBound : Context n m k -> CaptureSet n k -> CBound n k -> Prop where
  | subcapt: Subcapt Γ C1 C2 -> CaptureBound Γ C1 (CBound.upper C2)
  | subkind : CaptureKind Γ C K -> CaptureBound Γ C (CBound.kind K)

-- theorem CaptureKind.union_elim (hk: CaptureKind Γ (C1 ∪ C2) K) : (CaptureKind Γ C1 K) ∧ (CaptureKind Γ C2 K) := by
--   generalize h : C1 ∪ C2 = C at hk
--   induction hk <;> cases h
--   case sub hs hk ih =>
--     have ⟨h1, h2⟩ := ih (Eq.refl (C1 ∪ C2))
--     apply sub hs at h1
--     apply sub hs at h2
--     apply And.intro <;> assumption
--   case union h1 h2 ih1 ih2 => apply And.intro <;> assumption

-- theorem CaptureKind.subset (hk: CaptureKind Γ C2 K) (hsub: C1 ⊆ C2) : CaptureKind Γ C1 K := by
--   induction hsub
--   case empty => apply empty
--   case rfl => assumption
--   case union_l h1 h2 ih1 ih2 =>
--     apply union
--     apply ih1 hk
--     apply ih2 hk
--   case union_rl h ih =>
--     apply ih
--     cases hk
--     case union h1 h2 => assumption
--     case sub hs hk =>
--       have ⟨h1, _⟩ := hs.union_elim
--       apply sub hk h1
--   case union_rr h ih =>
--     apply ih
--     cases hk
--     case union h1 h2 => assumption
--     case sub hs hk =>
--       have ⟨_, h2⟩ := hs.union_elim
--       apply sub hk h2

-- theorem CaptureKind.subcapt  (hk: CaptureKind Γ C2 K) (hs: Subcapt Γ C1 C2): CaptureKind Γ C1 K := by
--   induction hs
--   case trans h1 h2 ih1 ih2 =>
--     apply ih1
--     apply ih2
--     apply hk
--   case subset hsub => apply hk.subset hsub
--   case union h1 h2 ih1 ih2 =>
--     apply union
--     apply ih1 hk
--     apply ih2 hk
--   case var hb =>
--     apply var hb hk
--   case cinstl hb =>
--     apply cinst
