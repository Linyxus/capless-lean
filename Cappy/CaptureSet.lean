import Capless.Tactics
import Capless.Basic
import Mathlib.Data.Fin.Basic
namespace Cappy

inductive CaptureSet : Nat -> Type where
| empty : CaptureSet n
| union : CaptureSet n -> CaptureSet n -> CaptureSet n
| singleton : Fin n -> CaptureSet n
| reach : Fin n -> CaptureSet n
| universal : CaptureSet n

@[simp]
instance : EmptyCollection (CaptureSet n) where
  emptyCollection := CaptureSet.empty

notation:max "{x=" x "}" => CaptureSet.singleton x
notation:max "{x*=" c "}" => CaptureSet.reach c
notation:max "{cap}" => CaptureSet.universal

@[simp]
instance : Union (CaptureSet n) where
  union := CaptureSet.union

inductive CaptureSet.Subset : CaptureSet n -> CaptureSet n -> Prop where
| empty : Subset {} C
| rfl : Subset C C
| union_l :
  Subset C1 C ->
  Subset C2 C ->
  Subset (C1 ∪ C2) C
| union_rl :
  Subset C C1 ->
  Subset C (C1 ∪ C2)
| union_rr :
  Subset C C2 ->
  Subset C (C1 ∪ C2)

@[simp]
instance : HasSubset (CaptureSet n) where
  Subset := CaptureSet.Subset

def CaptureSet.rename (C : CaptureSet n) (f : Capless.FinFun n n') : CaptureSet n' :=
  match C with
  | empty => {}
  | union C1 C2 => (C1.rename f) ∪ (C2.rename f)
  | singleton x => {x=(f x)}
  | reach x => {x*=(f x)}
  | universal => {cap}

end Cappy
