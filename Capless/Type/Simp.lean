import Capless.Type.Renaming
namespace Capless

/-!
# Simplification Lemmas

Useful equations for simplifying types.
-/

@[simp]
def EType.weaken_type :
  (EType.type T).weaken = EType.type (T.weaken) := by
  simp [EType.weaken, EType.rename, CType.weaken]

@[simp]
def CType.weaken_capt :
  (CType.capt C S).weaken = CType.capt C.weaken S.weaken := by
  simp [CType.weaken, CType.rename, SType.weaken, CaptureSet.weaken]

@[simp]
def EType.tweaken_type :
  (EType.type T).tweaken = EType.type (T.tweaken) := by
  simp [EType.tweaken, EType.trename, CType.tweaken]

@[simp]
def CType.tweaken_capt :
  (CType.capt C S).tweaken = CType.capt C S.tweaken := by
  simp [CType.tweaken, CType.trename, SType.tweaken]

@[simp]
def EType.cweaken_type :
  (EType.type T).cweaken = EType.type (T.cweaken) := by
  simp [EType.cweaken, EType.crename, CType.cweaken]

@[simp]
def CType.cweaken_capt :
  (CType.capt C S).cweaken = CType.capt C.cweaken S.cweaken := by
  simp [CType.cweaken, CType.crename, SType.cweaken, CaptureSet.cweaken]

@[simp]
def CBound.weaken_upper :
  (CBound.upper C).weaken = CBound.upper C.weaken := by
  simp [CBound.weaken, CBound.rename, CaptureSet.weaken]

@[simp]
def CBound.cweaken_upper :
  (CBound.upper C).cweaken = CBound.upper C.cweaken := by
  simp [CBound.cweaken, CBound.crename, CaptureSet.cweaken]

@[simp]
theorem SType.rename_label :
  (SType.label S).rename f = SType.label (S.rename f) := by
  simp [SType.rename]

theorem CType.rename_capt :
  (CType.capt C S).rename f = CType.capt (C.rename f) (S.rename f) := by simp [CType.rename]

end Capless
