import Capless.Renaming.Basic

/-!
# Basic Weakening Operations

This file defines fundamental weakening operations for variable mappings in the Capless type system.
Weakening allows extending typing contexts by adding new variables while preserving the validity
of existing judgments.

The file provides:
- `VarMap.weaken`, `VarMap.lweaken`: Basic variable map weakening for term and label variables
- `CVarMap.weaken`: Capture variable map weakening
- `TVarMap.weaken`: Type variable map weakening
- Extended weakening operations for nested contexts (`weaken_ext`, `weaken_cext_ext`, etc.)

These operations are essential for proving that typing judgments remain valid when new variables
are introduced into the context.
-/

namespace Capless

def VarMap.weaken {Γ : Context n m k} :
  VarMap Γ FinFun.weaken (Γ.var T) := by
  constructor <;> (intros; constructor; trivial)

def VarMap.lweaken {Γ : Context n m k} :
  VarMap Γ FinFun.weaken (Γ.label S) := by
  constructor <;> (intros; constructor; trivial)

def VarMap.weaken_ext {Γ : Context n m k} :
  VarMap
    (Γ.var T)
    FinFun.weaken.ext
    ((Γ.var P).var T.weaken) := by
  apply VarMap.ext
  apply VarMap.weaken

def VarMap.lweaken_ext {Γ : Context n m k} :
  VarMap
    (Γ.var T)
    FinFun.weaken.ext
    ((Γ.label P).var T.weaken) := by
  apply VarMap.ext
  apply VarMap.lweaken

def VarMap.weaken_cext_ext {Γ : Context n m k} :
  VarMap
    ((Γ.cvar (CBinding.bound b)).var T)
    FinFun.weaken.ext
    (((Γ.var P).cvar (CBinding.bound b.weaken)).var T.weaken) := by
  apply VarMap.ext
  apply VarMap.cext
  apply VarMap.weaken

def VarMap.lweaken_cext_ext {Γ : Context n m k} :
  VarMap
    ((Γ.cvar (CBinding.bound b)).var T)
    FinFun.weaken.ext
    (((Γ.label P).cvar (CBinding.bound b.weaken)).var T.weaken) := by
  apply VarMap.ext
  apply VarMap.cext
  apply VarMap.lweaken

def CVarMap.weaken {Γ : Context n m k} :
  CVarMap Γ FinFun.weaken (Γ.cvar b) := by
  constructor <;> (intros; constructor; trivial)

def CVarMap.weaken_ext {Γ : Context n m k} :
  CVarMap
    (Γ.var T)
    FinFun.weaken
    ((Γ.cvar b).var T.cweaken) := by
  apply CVarMap.ext
  apply CVarMap.weaken

theorem CBinding.cweaken_bound :
  (CBinding.bound b : CBinding n k).cweaken = (CBinding.bound b.cweaken) := by
  simp [CBinding.cweaken, CBinding.crename, CBound.cweaken]

def CVarMap.weaken_cext_ext {Γ : Context n m k} :
  CVarMap
    ((Γ.cvar (CBinding.bound B)).var T)
    FinFun.weaken.ext
    (((Γ.cvar b).cvar (CBinding.bound B.cweaken)).var T.cweaken1) := by
  rw [<- CBinding.cweaken_bound]
  apply CVarMap.ext
  apply CVarMap.cext
  apply CVarMap.weaken

def TVarMap.weaken {Γ : Context n m k} :
  TVarMap Γ FinFun.weaken (Γ.tvar b) := by
  constructor <;> (intros; constructor; trivial)

def TVarMap.weaken_ext {Γ : Context n m k} :
  TVarMap
    (Γ.var T)
    FinFun.weaken
    ((Γ.tvar b).var T.tweaken) := by
  apply TVarMap.ext
  apply TVarMap.weaken

def TVarMap.weaken_cext_ext {Γ : Context n m k} :
  TVarMap
    ((Γ.cvar (CBinding.bound B)).var T)
    FinFun.weaken
    (((Γ.tvar b).cvar (CBinding.bound B)).var T.tweaken) := by
  apply TVarMap.ext
  apply TVarMap.cext
  apply TVarMap.weaken

end Capless
