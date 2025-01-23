import Capybara.Syntax.CaptureSet.Core
namespace Capybara

/-!
# Properties of capture sets

## Renaming identity
We can show that renaming by the identity renaming yields the same capture set.
-/
@[simp]
theorem CaptureSet.rename_id {C : CaptureSet n k} : C.rename (Renaming.id (m:=m).asCapt) = C := by
  induction C <;> simp [CaptureSet.rename]
  case union ih1 ih2 => simp [ih1, ih2]
  case singleton => simp [Renaming.id, Renaming.asCapt, FinFun.id]
  case csingleton => simp [Renaming.id, Renaming.asCapt, FinFun.id]

/-!
## Composition of renamings
In the following, we show that renaming composes.
-/
theorem CaptureSet.rename_comp {ρ : CaptureRenaming n k n' k'} {ρ' : CaptureRenaming n' k' n'' k''} {C : CaptureSet n k} :
  (C.rename ρ).rename ρ' = C.rename (ρ.comp ρ') := by
  induction C <;> simp [CaptureSet.rename]
  case union ih1 ih2 => simp [ih1, ih2]
  case singleton => simp [CaptureRenaming.comp, FinFun.comp]
  case csingleton => simp [CaptureRenaming.comp, FinFun.comp]

theorem CaptureSet.rename_weaken {C : CaptureSet n k} {ρ : Renaming n m k n' m' k'} :
  (C.rename ρ.asCapt).weaken = C.weaken.rename ρ.ext.asCapt := by
  simp [CaptureSet.weaken]
  simp [CaptureSet.rename_comp]
  rw [Renaming.weaken_transportM (m1:=0) (m2:=m')]
  rw [<-Renaming.comp_asCapt]
  rw [Renaming.weaken_transportM (m1:=0) (m2:=m)]
  rw [<-Renaming.comp_asCapt]
  simp [Renaming.comp_weaken]

theorem CaptureSet.rename_cweaken {C : CaptureSet n k} {ρ : Renaming n m k n' m' k'} :
  (C.rename ρ.asCapt).cweaken = C.cweaken.rename ρ.cext.asCapt := by
  simp [CaptureSet.cweaken, CaptureSet.rename_comp]
  rw [Renaming.cweaken_transportM (m1:=0) (m2:=m')]
  rw [<-Renaming.comp_asCapt]
  rw [Renaming.cweaken_transportM (m1:=0) (m2:=m)]
  rw [<-Renaming.comp_asCapt]
  simp [Renaming.comp_cweaken]

theorem CaptureSet.rename_subset {C1 C2 : CaptureSet n k} {ρ : CaptureRenaming n k n' k'} (hs : C1 ⊆ C2) :
  (C1.rename ρ) ⊆ (C2.rename ρ) := by
  induction hs <;> try simp [CaptureSet.rename] <;> try (solve | constructor)
  case refl => apply Subset.refl
  case union_l ih1 ih2 => constructor <;> aesop
  case union_rl => apply Subset.union_rl; aesop
  case union_rr => apply Subset.union_rr; aesop

end Capybara
