import Mathlib.Data.Fin.Basic
import Capybara.Syntax.Type
namespace Capybara

/-!
Kind of a capture set parameter.
-/
inductive CKind : Nat -> Nat -> Type where
| Sep : SepDegree n k -> CKind n k
| Fresh : CKind n k

/-!
Type binding and capture set binding.

Type binding can be either a type parameter (abstract) or
a concrete type alias. Similarly, capture set binding can be
a capture set parameter (abstract) or a concrete capture set alias.
-/
inductive TBinding : Nat -> Nat -> Nat -> Type where
| param : SType n m k -> TBinding n m k
| alias : SType n m k -> TBinding n m k


inductive CBinding : Nat -> Nat -> Type where
| param : CKind n k -> CBinding n k
| alias : CaptureSet n k -> CBinding n k

notation:max "tparam" S => TBinding.param S
notation:max "talias" S => TBinding.alias S
notation:max "cparam" k => CBinding.param k
notation:max "calias" C => CBinding.alias C

/-!
Weakening functions for type and capture set binding.
-/
def TBinding.weaken : TBinding n m k -> TBinding (n+1) m k
| TBinding.param T => TBinding.param (T.weaken)
| TBinding.alias T => TBinding.alias (T.weaken)
def CKind.weaken : CKind n k -> CKind (n+1) k
| CKind.Sep D => CKind.Sep (D.weaken)
| CKind.Fresh => CKind.Fresh
def CBinding.weaken : CBinding n k -> CBinding (n+1) k
| CBinding.param k => CBinding.param (k.weaken)
| CBinding.alias C => CBinding.alias (C.weaken)
def TBinding.tweaken : TBinding n m k -> TBinding n (m+1) k
| TBinding.param T => TBinding.param (T.tweaken)
| TBinding.alias T => TBinding.alias (T.tweaken)
def TBinding.cweaken : TBinding n m k -> TBinding n m (k+1)
| TBinding.param T => TBinding.param (T.cweaken)
| TBinding.alias T => TBinding.alias (T.cweaken)
def CKind.cweaken : CKind n k -> CKind n (k+1)
| CKind.Sep D => CKind.Sep (D.cweaken)
| CKind.Fresh => CKind.Fresh
def CBinding.cweaken : CBinding n k -> CBinding n (k+1)
| CBinding.param k => CBinding.param (k.cweaken)
| CBinding.alias C => CBinding.alias (C.cweaken)

/-!
An indexed context. A `Context n m k` contains `n` term variables,
`m` type variables, and `k` capture set variables.
!-/
inductive Context : Nat -> Nat -> Nat -> Type where
| empty : Context 0 0 0
| cons : Context n m k -> CType n m k -> Context (n+1) m k
| tcons : Context n m k -> TBinding n m k -> Context n (m+1) k
| ccons : Context n m k -> CBinding n k -> Context n m (k+1)

instance : EmptyCollection (Context 0 0 0) :=
  ⟨Context.empty⟩

theorem Context.empty_def :
  ({} : Context 0 0 0) = Context.empty := rfl

notation:20 Γ ",x:" T => Context.cons Γ T
notation:20 Γ ",X:" T => Context.tcons Γ T
notation:20 Γ ",c:" C => Context.ccons Γ C

/-!
Context lookup.

`Context.Lookup`, `Context.LookupT`, and `Context.LookupC` look up the three dimensions of a context,
respectively.
-/
inductive Context.Lookup : Context n m k -> Fin n -> CType n m k -> Prop where
| here : Context.Lookup (Γ,x:T) 0 T.weaken
| there :
  Context.Lookup Γ x T ->
  Context.Lookup (Γ,x:T) (x.succ) T.weaken
| tthere :
  Context.Lookup Γ x T ->
  Context.Lookup (Γ,X:B) x (T.tweaken)
| cthere :
  Context.Lookup Γ x T ->
  Context.Lookup (Γ,c:B) x (T.cweaken)
inductive Context.LookupT : Context n m k -> Fin m -> TBinding n m k -> Prop where
| here : Context.LookupT (Γ,X:T) 0 T.tweaken
| there :
  Context.LookupT Γ X S ->
  Context.LookupT (Γ,x:T) X S.weaken
| tthere :
  Context.LookupT Γ X T ->
  Context.LookupT (Γ,X:B) (X.succ) T.tweaken
| cthere :
  Context.LookupT Γ X T ->
  Context.LookupT (Γ,c:B) X T.cweaken
inductive Context.LookupC : Context n m k -> Fin k -> CBinding n k -> Prop where
| here : Context.LookupC (Γ,c:C) 0 C.cweaken
| there :
  Context.LookupC Γ c C ->
  Context.LookupC (Γ,x:T) c C.weaken
| tthere :
  Context.LookupC Γ c C ->
  Context.LookupC (Γ,X:B) c C
| cthere :
  Context.LookupC Γ c C ->
  Context.LookupC (Γ,c:B) (c.succ) C.cweaken

end Capybara
