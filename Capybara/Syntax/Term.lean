import Capybara.Syntax.Type
namespace Capybara

inductive Term : Nat -> Nat -> Nat -> Type where
| var : Fin n -> Term n m k
| lam : CType n m k -> Term (n+1) m k -> Term n m k
| tlam : SType n m k -> Term n (m+1) k -> Term n m k
| clam : Kind -> Term n m (k+1) -> Term n m k
| pack : CaptureSet n k -> Fin n -> Term n m k
| app : Fin n -> Fin n -> Term n m k
| tapp : Fin n -> SType n m k -> Term n m k
| capp : Fin n -> CaptureSet n k -> Term n m k
| letin : Term n m k -> Term (n+1) m k -> Term n m k
| unpack : Term n m k -> Term (n+1) m (k+1) -> Term n m k

end Capybara
