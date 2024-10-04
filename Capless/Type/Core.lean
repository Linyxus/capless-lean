import Capless.CaptureSet
import Capless.Basic
namespace Capless
mutual

inductive EType : Nat -> Nat -> Nat -> Type where
| ex : CType n m (k+1) -> EType n m k
| type : CType n m k -> EType n m k

inductive CType : Nat -> Nat -> Nat -> Type where
| capt : CaptureSet n k -> SType n m k -> CType n m k

inductive SType : Nat -> Nat -> Nat -> Type where
| top : SType n m k
| tvar : Fin m -> SType n m k
| forall : CType n m k -> EType (n+1) m k -> SType n m k
| tforall : SType n m k -> EType n (m+1) k -> SType n m k
| cforall : EType n m (k+1) -> SType n m k
| box : CType n m k -> SType n m k
| label : SType n m k -> SType n m k

end

notation "⊤" => SType.top
notation:50 "∀(x:" T ")" U => SType.forall T U
notation:50 "∀[X<:" S "]" T => SType.tforall S T
notation:50 "∀[c]" T => SType.cforall T
notation:max S " ^ " C => CType.capt C S
notation:40 "∃c." T => EType.ex T
notation:40 "Label[" S "]" => SType.label S
notation:60 "□" T => SType.box T

instance : Coe (CType n m k) (EType n m k) where
  coe T := EType.type T

end Capless
