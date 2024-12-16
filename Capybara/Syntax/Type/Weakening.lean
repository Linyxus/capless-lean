import Capybara.Syntax.Type.Renaming
namespace Capybara

/-!
Term weakening functions.
-/
def EType.weaken : EType n m k -> EType (n+1) m k :=
  fun E => E.rename Renaming.weaken
def CType.weaken : CType n m k -> CType (n+1) m k :=
  fun T => T.rename Renaming.weaken
def SType.weaken : SType n m k -> SType (n+1) m k :=
  fun S => S.rename Renaming.weaken

/-!
Type weakening functions.
-/
def EType.tweaken : EType n m k -> EType n (m+1) k :=
  fun E => E.rename Renaming.tweaken
def CType.tweaken : CType n m k -> CType n (m+1) k :=
  fun T => T.rename Renaming.tweaken
def SType.tweaken : SType n m k -> SType n (m+1) k :=
  fun S => S.rename Renaming.tweaken

/-!
Capture set weakening functions.
-/
def EType.cweaken : EType n m k -> EType n m (k+1) :=
  fun E => E.rename Renaming.cweaken
def CType.cweaken : CType n m k -> CType n m (k+1) :=
  fun T => T.rename Renaming.cweaken
def SType.cweaken : SType n m k -> SType n m (k+1) :=
  fun S => S.rename Renaming.cweaken

end Capybara
