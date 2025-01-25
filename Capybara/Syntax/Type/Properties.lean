import Capybara.Syntax.CaptureSet
import Capybara.Syntax.Type.Renaming
import Capybara.Syntax.Type.Weakening
namespace Capybara


/-!
# Basic properties of type renamings

## Renaming identity
First, we show that renaming by the identity renaming yields the separation degree.
-/
theorem SepDegree.rename_id {D : SepDegree n k} : D.rename (Renaming.id (m:=m)).asCapt = D := by
  cases D; simp [SepDegree.rename]

/-!
Then, we show that renaming by the identity renaming yields the type.
-/
mutual

theorem EType.rename_id {E : EType n m k} : E.rename Renaming.id = E :=
  match E with
  | .ex T => by
    simp [EType.rename]
    simp [Renaming.id_cext]
    simp [CType.rename_id]
  | .type T => by
    simp [EType.rename]
    simp [CType.rename_id]

theorem CType.rename_id {C : CType n m k} : C.rename Renaming.id = C :=
  match C with
  | .capt C' m S => by
    simp [CType.rename]
    simp [SType.rename_id]

theorem SType.rename_id {S : SType n m k} : S.rename Renaming.id = S :=
  match S with
  | .top => rfl
  | .tvar i => by
    simp [SType.rename, Renaming.id]
    rfl
  | .tarrow S' T => by
    simp [SType.rename]
    simp [Renaming.id_text]
    simp [SType.rename_id, EType.rename_id]
  | .arrow C T => by
    simp [SType.rename]
    simp [Renaming.id_ext]
    simp [CType.rename_id, EType.rename_id]
  | .carrow D T => by
    simp [SType.rename]
    simp [Renaming.id_cext]
    simp [EType.rename_id, SepDegree.rename_id]
  | .farrow C T => by
    simp [SType.rename]
    simp [Renaming.id_cext, Renaming.id_ext]
    simp [CType.rename_id, EType.rename_id]

end

/-!
## Renaming composition
-/
theorem SepDegree.rename_comp {D : SepDegree n k} :
  (D.rename ρ).rename ρ' = D.rename (ρ.comp ρ') := by
  cases D; simp [SepDegree.rename, CaptureSet.rename_comp]

mutual

theorem EType.rename_comp {E : EType n m k} :
  (E.rename ρ).rename ρ' = E.rename (ρ.comp ρ') :=
  match E with
  | .type T => by
    simp [EType.rename]
    simp [CType.rename_comp]
  | .ex T => by
    simp [EType.rename]
    simp [CType.rename_comp, Renaming.comp_cext]

theorem CType.rename_comp {C : CType n m k} :
  (C.rename ρ).rename ρ' = C.rename (ρ.comp ρ') :=
  match C with
  | .capt m' C' S => by
    simp [CType.rename, SType.rename_comp]
    simp [CaptureSet.rename_comp, Renaming.comp_asCapt]

theorem SType.rename_comp {S : SType n m k} :
  (S.rename ρ).rename ρ' = S.rename (ρ.comp ρ') :=
  match S with
  | .top => by
    simp [SType.rename]
  | .tvar i => by
    simp [SType.rename, Renaming.comp, FinFun.comp]
  | .tarrow S' T => by
    simp [SType.rename]
    simp [SType.rename_comp, EType.rename_comp, Renaming.comp_text]
  | .arrow C T => by
    simp [SType.rename]
    simp [CType.rename_comp, EType.rename_comp, Renaming.comp_ext]
  | .carrow D T => by
    simp [SType.rename]
    simp [EType.rename_comp, SepDegree.rename_comp, Renaming.comp_cext, Renaming.comp_asCapt]
  | .farrow C T => by
    simp [SType.rename]
    simp [CType.rename_comp, EType.rename_comp, Renaming.comp_cext, Renaming.comp_ext]

end

/-!
## Corollaries of renaming composition
-/
theorem CType.rename_weaken {T : CType n m k} :
  (T.rename ρ).weaken = T.weaken.rename ρ.ext := by
  simp [CType.weaken, CType.rename_comp, Renaming.comp_weaken]

theorem CType.rename_tweaken {T : CType n m k} :
  (T.rename ρ).tweaken = T.tweaken.rename ρ.text := by
  simp [CType.tweaken, CType.rename_comp, Renaming.comp_tweaken]

theorem CType.rename_cweaken {T : CType n m k} :
  (T.rename ρ).cweaken = T.cweaken.rename ρ.cext := by
  simp [CType.cweaken, CType.rename_comp, Renaming.comp_cweaken]

theorem SType.rename_weaken {S : SType n m k} :
  (S.rename ρ).weaken = S.weaken.rename ρ.ext := by
  simp [SType.weaken, SType.rename_comp, Renaming.comp_weaken]

theorem SType.rename_tweaken {S : SType n m k} :
  (S.rename ρ).tweaken = S.tweaken.rename ρ.text := by
  simp [SType.tweaken, SType.rename_comp, Renaming.comp_tweaken]

theorem SType.rename_cweaken {S : SType n m k} :
  (S.rename ρ).cweaken = S.cweaken.rename ρ.cext := by
  simp [SType.cweaken, SType.rename_comp, Renaming.comp_cweaken]

end Capybara
