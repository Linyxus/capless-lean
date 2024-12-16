import Capybara.Syntax.Mode
import Capybara.Morphism.Core
namespace Capybara

/-!
Capture set definitions.
-/
inductive CaptureSet : Nat -> Nat -> Type where
| empty : CaptureSet n k
| union : CaptureSet n k -> CaptureSet n k -> CaptureSet n k
| singleton : Fin n -> Mode -> CaptureSet n k
| csingleton : Fin k -> Mode -> CaptureSet n k

/-!
Instance definitions for capture sets.
-/
instance : EmptyCollection (CaptureSet n k) where
  emptyCollection := CaptureSet.empty

instance : Union (CaptureSet n k) where
  union := CaptureSet.union

/-!
Notation for capture sets.
-/
notation:40 "{x@" m ":=" x "}" => CaptureSet.singleton x m
notation:40 "{x=" x "}" => {x@ε:=x}
notation:40 "{c@" m ":=" x "}" => CaptureSet.csingleton x m
notation:40 "{c=" x "}" => {c@ε:=x}

/-!
Renaming functions for capture sets.
-/
def CaptureSet.rename
  (C : CaptureSet n k)
  (ρ : Renaming n m k n' m' k') :
  CaptureSet n' k' :=
  match C with
  | empty => {}
  | union C1 C2 => (C1.rename ρ) ∪ (C2.rename ρ)
  | singleton x m => {x@m:=ρ.var x}
  | csingleton x m => {c@m:=ρ.cvar x}

/-!
Mode qualification.
-/
def CaptureSet.qualified
  (C : CaptureSet n k)
  (m : Mode) :
  CaptureSet n k :=
  match C, m with
  | empty, _ => {}
  | union C1 C2, m => (C1.qualified m) ∪ (C2.qualified m)
  | singleton x m0, ε => singleton x m0
  | singleton x _, m => singleton x m
  | csingleton x m0, ε => csingleton x m0
  | csingleton x _, m => csingleton x m

/-!
Weakening functions for capture sets.
-/
def CaptureSet.weaken : CaptureSet n k -> CaptureSet (n+1) k :=
  fun C => C.rename (Renaming.weaken (m:=0))
def CaptureSet.cweaken : CaptureSet n k -> CaptureSet n (k+1) :=
  fun C => C.rename (Renaming.cweaken (m:=0))

/-!
Basic theorems.
-/
theorem CaptureSet.empty_def :
  ({} : CaptureSet n k) = CaptureSet.empty := rfl

theorem CaptureSet.union_def (C1 C2 : CaptureSet n k) :
  (C1 ∪ C2) = CaptureSet.union C1 C2 := rfl

@[simp]
theorem CaptureSet.qualified_default {C : CaptureSet n k} :
  C.qualified ε = C := by
  induction C <;> simp [CaptureSet.qualified, CaptureSet.empty_def]
  case union ih1 ih2 => simp [CaptureSet.union_def, ih1, ih2]

end Capybara
