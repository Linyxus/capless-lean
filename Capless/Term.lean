import Capless.CaptureSet
import Capless.Type
namespace Capless

inductive Term : Nat -> Nat -> Nat -> Type where
| var : Fin n -> Term n m k
| lam : EType n m k -> Term (n+1) m k -> Term n m k
| tlam : SType n m k -> Term n (m+1) k -> Term n m k
| clam : Term n m (k+1) -> Term n m k
| boxed : Fin n -> Term n m k
| pack : Fin k -> Fin n -> Term n m k
| app : Fin n -> Fin n -> Term n m k
| tapp : Fin n -> Fin m -> Term n m k
| capp : Fin n -> Fin k -> Term n m k
| letin : Term n m k -> Term (n+1) m k -> Term n m k
| bindt : SType n m k -> Term n (m+1) k -> Term n m k
| bindc : CaptureSet n k -> Term n m (k+1) -> Term n m k
| unbox : CaptureSet n k -> Fin n -> Term n m k

inductive Term.IsValue : Term n m k -> Prop where
| lam : Term.IsValue (lam E t)
| tlam : Term.IsValue (tlam S t)
| clam : Term.IsValue (clam t)
| boxed : Term.IsValue (boxed x)
| pack : Term.IsValue (pack c x)

end Capless
