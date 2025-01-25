import Capybara.Syntax.CaptureSet.Core
namespace Capybara

inductive SepMode : Type where
| Mut : SepMode
| Imm : SepMode

/-!
Separation degree.
-/
structure SepDegree (n k : Nat) : Type where
  mode : SepMode
  degree : CaptureSet n k

mutual

inductive EType : Nat -> Nat -> Nat -> Type where
| type : CType n m k -> EType n m k
| ex   : CType n m (k+1) -> EType n m k

inductive CType : Nat -> Nat -> Nat -> Type where
| capt : CaptureSet n k -> Mutability -> SType n m k -> CType n m k

inductive SType : Nat -> Nat -> Nat -> Type where
| top : SType n m k
| tvar : Fin m -> SType n m k
| tarrow : SType n m k -> EType n (m+1) k -> SType n m k
| arrow : CType n m k -> EType (n+1) m k -> SType n m k
| carrow : SepDegree n k -> EType n m (k+1) -> SType n m k
| farrow : CType n m (k+1) -> EType (n+1) m (k+1) -> SType n m k

end

/-!
Notation for types.
-/
notation:max "⊤" => SType.top
notation:40 "[X<:" S "]->" T => SType.tarrow S T
notation:40 "(x:" S ")->" T => SType.arrow S T
notation:40 "[c:" D "]->" T => SType.carrow D T
notation:40 "[c:Fresh](x:" T ")->" E => SType.farrow T E
notation:50 S "^[" m "]" C => CType.capt C m S
notation:50 S "^" C => CType.capt C ε S

end Capybara
