import Mathlib.Data.Fin.Basic
namespace ExpWeaken

inductive CaptureSet : Nat -> Type where
| empty : CaptureSet n
| union : CaptureSet n -> CaptureSet n -> CaptureSet n
| zero : CaptureSet 1
| weaken : CaptureSet n -> CaptureSet (n+1)

instance : EmptyCollection (CaptureSet n) where
  emptyCollection := CaptureSet.empty

instance : Union (CaptureSet n) where
  union := CaptureSet.union

notation:max C "↑" => CaptureSet.weaken C

inductive CaptureSet.Subset : CaptureSet n -> CaptureSet n -> Prop where
| refl : CaptureSet.Subset C C
| union_l :
  CaptureSet.Subset C1 C ->
  CaptureSet.Subset C2 C ->
  CaptureSet.Subset (C1 ∪ C2) C
| union_r1 :
  CaptureSet.Subset C C1 ->
  CaptureSet.Subset C (C1 ∪ C2)
| union_r2 :
  CaptureSet.Subset C C2 ->
  CaptureSet.Subset C (C1 ∪ C2)
| weaken_union :
  CaptureSet.Subset (C1↑ ∪ C2↑) C ->
  CaptureSet.Subset (C1 ∪ C2)↑ C
| weaken_elim :
  CaptureSet.Subset C1 C2 ->
  CaptureSet.Subset C1↑ C2↑

instance : HasSubset (CaptureSet n) where
  Subset := CaptureSet.Subset

mutual

inductive CType0 : Nat -> Nat -> Type where
| capt : CaptureSet n -> SType0 n m -> CType0 n m
| weaken : CType0 n m -> CType0 (n+1) m
| tweaken : CType0 n m -> CType0 n (m+1)

inductive SType0 : Nat -> Nat -> Type where
| top : SType0 n m
| tvar : Fin m -> SType0 n m
| box : CType0 n m -> SType0 n m
| arrow : CType0 n m -> CType0 (n+1) m -> SType0 n m
| tarrow : SType0 n m -> CType0 n (m+1) -> SType0 n m
| weaken : SType0 n m -> SType0 (n+1) m
| tweaken : SType0 n m -> SType0 n (m+1)

end

end ExpWeaken
