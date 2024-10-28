import Cappy.Syntax.Type
namespace Cappy

inductive Term : Nat -> Nat -> Type where
| var : Fin n -> Term n m
| abs : Annot -> CType n m -> Term (n+1) m -> Term n m
| app : Fin n -> Fin n -> Term n m
| tabs : SType n m -> Term n (m+1) -> Term n m
| tapp : Fin m -> SType n m -> Term n m
| box : Fin n -> Term n m
| unbox : CaptureSet n -> Fin n -> Term n m
| letin : Term n m -> Term (n+1) m -> Term n m

end Cappy
