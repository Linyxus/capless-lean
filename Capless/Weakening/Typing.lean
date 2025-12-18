import Capless.Weakening.Basic
import Capless.Renaming.Term.Typing
import Capless.Renaming.Type.Typing
import Capless.Renaming.Capture.Typing

/-!
# Typing Weakening

This file establishes weakening properties for typing judgments in the Capless type system.
The main result is that well-typed terms remain well-typed when the context is extended
with new variables.

The file provides comprehensive weakening operations for `Typed` judgments:

## Basic weakening:
- `Typed.weaken`: Extend context with a new term variable
- `Typed.lweaken`: Extend context with a new label variable
- `Typed.tweaken`: Extend context with a new type variable
- `Typed.cweaken`: Extend context with a new capture variable

## Extended weakening:
- `Typed.weaken_ext`, `Typed.lweaken_ext`: For nested variable contexts
- `Typed.weaken_cext_ext`, `Typed.lweaken_cext_ext`: For capture-extended contexts
- `Typed.weaken_text_ext_ext`, `Typed.lweaken_text_ext_ext`, `Typed.cweaken_text_ext_ext`, `Typed.tweaken_text_ext_ext`: For type-var then two var contexts (handler bindings)
- `Typed.tweaken_ext`, `Typed.tweaken_cext_ext`: For type variable extensions
- `Typed.cweaken_ext`, `Typed.cweaken_cext_ext`: For capture variable extensions

These operations are fundamental to proving type preservation and other soundness properties.
-/

namespace Capless

theorem Typed.weaken
  (h : Typed Γ t E Ct) :
  Typed (Γ.var T) t.weaken E.weaken Ct.weaken := by
  simp [Term.weaken, EType.weaken]
  apply Typed.rename h
  apply VarMap.weaken

theorem Typed.lweaken
  (h : Typed Γ t E Ct) :
  Typed (Γ.label c S) t.weaken E.weaken Ct.weaken := by
  simp [Term.weaken, EType.weaken]
  apply h.rename
  apply VarMap.lweaken

theorem Typed.weaken_ext {Γ : Context n m k}
  (h : Typed (Γ.var T) t E Ct) :
  Typed ((Γ.var P).var T.weaken) t.weaken1 E.weaken1 Ct.weaken1 := by
  simp [Term.weaken1, EType.weaken1, CaptureSet.weaken1]
  apply h.rename VarMap.weaken_ext

theorem Typed.lweaken_ext {Γ : Context n m k}
  (h : Typed (Γ.var T) t E Ct) :
  Typed ((Γ.label c P).var T.weaken) t.weaken1 E.weaken1 Ct.weaken1 := by
  simp [Term.weaken1, EType.weaken1]
  apply h.rename VarMap.lweaken_ext

theorem Typed.weaken_cext_ext {Γ : Context n m k}
  (h : Typed ((Γ.cvar (CBinding.bound B)).var T) t E Ct) :
  Typed (((Γ.var P).cvar (CBinding.bound B.weaken)).var T.weaken) t.weaken1 E.weaken1 Ct.weaken1 := by
  simp [Term.weaken1, EType.weaken1]
  apply h.rename VarMap.weaken_cext_ext

theorem Typed.lweaken_cext_ext {Γ : Context n m k}
  (h : Typed ((Γ.cvar (CBinding.bound B)).var T) t E Ct) :
  Typed (((Γ.label c P).cvar (CBinding.bound B.weaken)).var T.weaken) t.weaken1 E.weaken1 Ct.weaken1 := by
  simp [Term.weaken1, EType.weaken1]
  apply h.rename VarMap.lweaken_cext_ext

theorem Typed.weaken_text_ext_ext {Γ : Context n m k}
  (h : Typed (((Γ.tvar b).var T1).var T2) t E Ct) :
  Typed ((((Γ.var P).tvar (b.rename FinFun.weaken)).var (T1.rename FinFun.weaken)).var (T2.rename FinFun.weaken.ext))
    (t.rename FinFun.weaken.ext.ext) (E.rename FinFun.weaken.ext.ext) (Ct.rename FinFun.weaken.ext.ext) := by
  apply h.rename VarMap.weaken_text_ext_ext

theorem Typed.lweaken_text_ext_ext {Γ : Context n m k}
  (h : Typed (((Γ.tvar b).var T1).var T2) t E Ct) :
  Typed ((((Γ.label c P).tvar (b.rename FinFun.weaken)).var (T1.rename FinFun.weaken)).var (T2.rename FinFun.weaken.ext))
    (t.rename FinFun.weaken.ext.ext) (E.rename FinFun.weaken.ext.ext) (Ct.rename FinFun.weaken.ext.ext) := by
  apply h.rename VarMap.lweaken_text_ext_ext

def Typed.cweaken_text_ext_ext {Γ : Context n m k}
  (h : Typed (((Γ.tvar b).var T1).var T2) t E Ct) :
  Typed ((((Γ.cvar cb).tvar (b.crename FinFun.weaken)).var T1.cweaken).var T2.cweaken)
    t.cweaken E.cweaken Ct.cweaken := by
  apply h.crename CVarMap.weaken_text_ext_ext

def Typed.tweaken_text_ext_ext {Γ : Context n m k}
  (h : Typed (((Γ.tvar b1).var T1).var T2) t E Ct) :
  Typed ((((Γ.tvar b2).tvar (b1.trename FinFun.weaken)).var (T1.trename FinFun.weaken.ext)).var (T2.trename FinFun.weaken.ext))
    (t.trename FinFun.weaken.ext) (E.trename FinFun.weaken.ext) Ct := by
  apply h.trename TVarMap.weaken_text_ext_ext

def Typed.tweaken
  (h : Typed Γ t E Ct) :
  Typed (Γ.tvar b) t.tweaken E.tweaken Ct := by
  simp [Term.tweaken, EType.tweaken]
  apply h.trename
  apply TVarMap.weaken

theorem Typed.tweaken_ext {Γ : Context n m k}
  (h : Typed (Γ.var T) t E Ct) :
  Typed ((Γ.tvar b).var T.tweaken) t.tweaken E.tweaken Ct := by
  simp [Term.tweaken, EType.tweaken]
  apply h.trename TVarMap.weaken_ext

theorem Typed.tweaken_cext_ext {Γ : Context n m k}
  (h : Typed ((Γ.cvar (CBinding.bound B)).var T) t E Ct) :
  Typed (((Γ.tvar b).cvar (CBinding.bound B)).var T.tweaken) t.tweaken E.tweaken Ct := by
  simp [Term.tweaken, EType.tweaken]
  apply h.trename TVarMap.weaken_cext_ext

def Typed.cweaken
  (h : Typed Γ t E Ct) :
  Typed (Γ.cvar b) t.cweaken E.cweaken Ct.cweaken := by
  simp [Term.cweaken, EType.cweaken]
  apply h.crename
  apply CVarMap.weaken

def Typed.cweaken_ext {Γ : Context n m k}
  (h : Typed (Γ.var T) t E Ct) :
  Typed ((Γ.cvar b).var T.cweaken) t.cweaken E.cweaken Ct.cweaken := by
  simp [Term.cweaken, EType.cweaken]
  apply h.crename CVarMap.weaken_ext

def Typed.cweaken_cext_ext {Γ : Context n m k}
  (h : Typed ((Γ.cvar (CBinding.bound B)).var T) t E Ct) :
  Typed (((Γ.cvar b).cvar (CBinding.bound B.cweaken)).var T.cweaken1) t.cweaken1 E.cweaken1 Ct.cweaken1 := by
  simp [Term.cweaken, EType.cweaken1]
  apply h.crename CVarMap.weaken_cext_ext

end Capless
