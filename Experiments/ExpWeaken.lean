import Mathlib.Data.Fin.Basic
namespace ExpWeaken

inductive CaptureSet0 : Nat -> Type where
| empty : CaptureSet0 n
| union : CaptureSet0 n -> CaptureSet0 n -> CaptureSet0 n
| zero : CaptureSet0 1
| weaken : CaptureSet0 n -> CaptureSet0 (n+1)

instance : EmptyCollection (CaptureSet0 n) where
  emptyCollection := CaptureSet0.empty

instance : Union (CaptureSet0 n) where
  union := CaptureSet0.union

notation:max C "↑" => CaptureSet0.weaken C

@[aesop safe [constructors]]
inductive CaptureSet0.Simp : CaptureSet0 n -> CaptureSet0 n -> Prop where
| refl : CaptureSet0.Simp C C
| union :
  CaptureSet0.Simp C1 C1' ->
  CaptureSet0.Simp C2 C2' ->
  CaptureSet0.Simp (C1 ∪ C2) (C1' ∪ C2')
| weaken_empty :
  CaptureSet0.Simp {}↑ {}
| weaken_union :
  CaptureSet0.Simp (C1 ∪ C2)↑ (C1'↑ ∪ C2'↑)

@[aesop unsafe [50% constructors]]
inductive CaptureSet0.Rewrite : CaptureSet0 n -> CaptureSet0 n -> Prop where
| simp :
  CaptureSet0.Simp C C' ->
  CaptureSet0.Rewrite C C'
| symm :
  CaptureSet0.Rewrite C1 C2 ->
  CaptureSet0.Rewrite C2 C1
| trans :
  CaptureSet0.Rewrite C1 C2 ->
  CaptureSet0.Rewrite C2 C3 ->
  CaptureSet0.Rewrite C1 C3

def CaptureSet0.rewrite_equiv : Equivalence (α:=CaptureSet0 n) CaptureSet0.Rewrite :=
  by constructor <;> aesop

def CaptureSet0.isSetoid : Setoid (CaptureSet0 n) :=
  ⟨CaptureSet0.Rewrite, CaptureSet0.rewrite_equiv⟩

def CaptureSet (n : Nat) : Type :=
  Quotient (CaptureSet0.isSetoid (n:=n))

mutual

inductive CType0 : Nat -> Nat -> Type where
| capt : CaptureSet0 n -> SType0 n m -> CType0 n m
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
