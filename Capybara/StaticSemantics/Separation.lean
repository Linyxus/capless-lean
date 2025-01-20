import Capybara.StaticSemantics.ReachRoot
namespace Capybara

-- /-!
-- Separation checking for capture roots.
-- -/
-- def CaptureRoot.Separation (Γ : Context n m k) (D1 D2 : CaptureRoot k) : Prop :=
--   -- Two capture roots are separated if given any shared access m1 c and m2 c,
--   ∀m1 m2 c, HasElem D1 c m1 -> HasElem D2 c m2 ->
--     -- either both are read-only, or
--     ((m1 = ro ∧ m2 = ro) ∨
--     -- c is an immutable capture variable
--     (Γ.LookupC c (cparam Kind.Imm)))

-- inductive CaptureSet.Separation : Context n m k -> CaptureSet n k -> CaptureSet n k -> Prop where
-- | mk :
--   CaptureSet.Root C1 Γ D1 ->
--   CaptureSet.Root C2 Γ D2 ->
--   CaptureRoot.Separation Γ D1 D2 ->
--   CaptureSet.Separation Γ C1 C2

-- notation:50 Γ " ⊢ " C1 " ⋈ " C2 => CaptureSet.Separation Γ C1 C2

end Capybara
