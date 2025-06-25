import Capless.CaptureSet
import Capless.Basic
namespace Capless

/-!
# Types in System Capless

## Main Definitions

`CBound`, `EType`, `CType`, and `SType` inductively define the syntax of types (Fig. 1) in System Capless. They are all parameterized by the number of binders in scope, so they are well-formed by construction.

`EType n m k`, `CType n m k`, and `SType n m k` are the inductive definitions of existential types, capturing types, and shape types, respectively, and they are defined in a context with `n` term variables, `m` type variables, and `k` capture variables.

`CBound n k` represents a capture bound in a context with `n` term variables and `k` capture variables. Note that it is only indexed by two numbers since the number of type variables is irrelevant to capture bounds.
-/

mutual

/-- Capture bound. -/
inductive CBound : Nat -> Nat -> Type where
| upper : CaptureSet n k -> CBound n k
| star : CBound n k

/-- Existential type. -/
inductive EType : Nat -> Nat -> Nat -> Type where
| ex : CType n m (k+1) -> EType n m k
| type : CType n m k -> EType n m k

/-- Capturing type. -/
inductive CType : Nat -> Nat -> Nat -> Type where
| capt : CaptureSet n k -> SType n m k -> CType n m k

/-- Shape type. -/
inductive SType : Nat -> Nat -> Nat -> Type where
| top : SType n m k
| tvar : Fin m -> SType n m k
| forall : CType n m k -> EType (n+1) m k -> SType n m k
| tforall : SType n m k -> EType n (m+1) k -> SType n m k
| cforall : CBound n k -> EType n m (k+1) -> SType n m k
| box : CType n m k -> SType n m k
| label : SType n m k -> SType n m k

end

/-!
## Notations and Instances
-/

notation "⊤" => SType.top
notation:50 "∀(x:" T ")" U => SType.forall T U
notation:50 "∀[X<:" S "]" T => SType.tforall S T
notation:50 "∀[c<:" B "]" T => SType.cforall B T
notation:max S " ^ " C => CType.capt C S
notation:40 "∃c." T => EType.ex T
notation:40 "Label[" S "]" => SType.label S
notation:60 "□" T => SType.box T

instance : Coe (CType n m k) (EType n m k) where
  coe T := EType.type T

end Capless
