import Capybara.Syntax.CaptureSet.Core
namespace Capybara

/-!
Kinds of capture set parameters.
-/
inductive Kind : Type where
| Imm : Kind
| Mut : Kind
| Fresh : Kind

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
| carrow : Kind -> EType n m (k+1) -> SType n m k

end

/-!
Notation for types.
-/
notation:max "⊤" => SType.top
notation:40 "[X<:" S "]->" T => SType.tarrow S T
notation:40 "(x:" S ")->" T => SType.arrow S T
notation:40 "[c:" S "]->" T => SType.carrow S T
notation:50 S "^[" m "]" C => CType.capt C m S
notation:50 S "^" C => CType.capt C ε S

end Capybara
