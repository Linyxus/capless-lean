import Capybara.Syntax.CaptureSet.Core
namespace Capybara

/-!
# Properties of capture sets

## Renaming identity
We can show that renaming by the identity renaming yields the same capture set.
-/
@[simp]
theorem CaptureSet.rename_id {C : CaptureSet n k} : C.rename (Renaming.id (m:=m)) = C := by
  induction C <;> simp [CaptureSet.rename]
  case union ih1 ih2 => simp [ih1, ih2]
  case singleton => simp [Renaming.id, FinFun.id]
  case csingleton => simp [Renaming.id, FinFun.id]

/-!
## Composition of renamings
In the following, we show that renaming composes.
-/
theorem CaptureSet.rename_comp {C : CaptureSet n k} :
  (C.rename ρ).rename ρ' = C.rename (ρ.comp ρ') := by
  induction C <;> simp [CaptureSet.rename]
  case union ih1 ih2 => simp [ih1, ih2]
  case singleton => simp [Renaming.comp, FinFun.comp]
  case csingleton => simp [Renaming.comp, FinFun.comp]

end Capybara
