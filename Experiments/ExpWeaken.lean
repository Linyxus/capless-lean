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
| empty : CaptureSet.Subset {} C
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
| weaken :
  CaptureSet.Subset C1 C2 ->
  CaptureSet.Subset C1↑ C2↑

instance : HasSubset (CaptureSet n) where
  Subset := CaptureSet.Subset

mutual

inductive CType : Nat -> Nat -> Type where
| capt : CaptureSet n -> SType n m -> CType n m
| weaken : CType n m -> CType (n+1) m
| tweaken : CType n m -> CType n (m+1)

inductive SType : Nat -> Nat -> Type where
| top : SType n m
| tvar : Fin m -> SType n m
| box : CType n m -> SType n m
| arrow : CType n m -> CType (n+1) m -> SType n m
| tarrow : SType n m -> CType n (m+1) -> SType n m
| weaken : SType n m -> SType (n+1) m
| tweaken : SType n m -> SType n (m+1)

end

inductive Context : Nat -> Nat -> Type where
| empty : Context 0 0
| cons : Context n m -> CType n m -> Context (n+1) m
| tcons : Context n m -> SType n m -> Context n (m+1)

inductive Subcapture : Context n m -> CaptureSet n -> CaptureSet n -> Prop where
| trans :
  Subcapture Γ C1 C2 ->
  Subcapture Γ C2 C3 ->
  Subcapture Γ C1 C3
| subset :
  C1 ⊆ C2 ->
  Subcapture Γ C1 C2
| union :
  Subcapture Γ C1 C ->
  Subcapture Γ C2 C ->
  Subcapture Γ (C1 ∪ C2) C

end ExpWeaken
