import Cappy.Syntax.Type.Core
namespace Cappy

mutual

theorem CType.rename_comp {T : CType n m} :
  (T.rename f).rename g = T.rename (g.comp f) :=
  match T with
  | CType.capt C S => by
    simp [CType.rename]
    apply And.intro
    { apply CaptureSet.rename_comp }
    { apply SType.rename_comp }

theorem SType.rename_comp {S : SType n m} :
  (S.rename f).rename g = S.rename (g.comp f) :=
  match S with
  | SType.top => by simp [SType.rename]
  | SType.tvar X => by simp [SType.rename, RenameFun.comp]
  | SType.arrow a T U => by
    simp [SType.rename]
    apply And.intro
    { apply CType.rename_comp }
    { simp [RenameFun.comp_ext]
      apply CType.rename_comp }
  | SType.tarrow S T => by
    simp [SType.rename]
    apply And.intro
    { apply SType.rename_comp }
    { simp [RenameFun.comp_text]
      apply CType.rename_comp }
  | SType.boxed T => by
    simp [SType.rename]
    apply CType.rename_comp

end

theorem CType.tweaken_weaken {T : CType n m} :
  T.weaken.tweaken = T.tweaken.weaken := by
  simp [CType.weaken, CType.tweaken]
  simp [CType.rename_comp]
  simp [RenameFun.weaken_tweaken]

end Cappy
