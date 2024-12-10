import Capybara.Syntax.Mode
import Capybara.Morphism.Core
namespace Capybara

inductive CaptureSet : Nat -> Nat -> Type where
| empty : CaptureSet n k
| union : CaptureSet n k -> CaptureSet n k -> CaptureSet n k
| singleton : Fin n -> Mode -> CaptureSet n k
| csingleton : Fin k -> Mode -> CaptureSet n k

instance : EmptyCollection (CaptureSet n k) where
  emptyCollection := CaptureSet.empty

instance : Union (CaptureSet n k) where
  union := CaptureSet.union

notation:40 "{x@" m ":=" x "}" => CaptureSet.singleton x m
notation:40 "{x=" x "}" => {x@ε:=x}
notation:40 "{c@" m ":=" x "}" => CaptureSet.csingleton x m
notation:40 "{c=" x "}" => {c@ε:=x}

def CaptureSet.rename (C : CaptureSet n k) (f : Fin n -> Fin n') : CaptureSet n' k :=
  match C with
  | empty => {}
  | union C1 C2 => (C1.rename f) ∪ (C2.rename f)
  | singleton x m => {x@m:=f x}
  | csingleton x m => {c@m:=x}

def CaptureSet.crename (C : CaptureSet n k) (f : Fin k -> Fin k') : CaptureSet n k' :=
  match C with
  | empty => {}
  | union C1 C2 => (C1.crename f) ∪ (C2.crename f)
  | singleton x m => {x@m:=x}
  | csingleton x m => {c@m:=f x}

end Capybara
