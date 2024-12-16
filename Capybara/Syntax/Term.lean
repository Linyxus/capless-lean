import Capybara.Syntax.Type
namespace Capybara

inductive Term : Nat -> Nat -> Nat -> Type where
| var : Fin n -> Term n m k
| lam : CType n m k -> Term (n+1) m k -> Term n m k
| tlam : SType n m k -> Term n (m+1) k -> Term n m k
| clam : Kind -> Term n m (k+1) -> Term n m k
| pack : Fin k -> Fin n -> Term n m k
| app : Fin n -> Fin n -> Term n m k
| tapp : Fin n -> Fin m -> Term n m k
| capp : Fin n -> Fin k -> Term n m k
| letin : Term n m k -> Term (n+1) m k -> Term n m k
| unpack : Term n m k -> Term (n+1) m (k+1) -> Term n m k
| bindc : CaptureSet n k -> Term n m (k+1) -> Term n m k
| bindt : SType n m k -> Term n (m+1) k -> Term n m k

def Term.rename
  (t : Term n m k)
  (ρ : Renaming n m k n' m' k') :
  Term n' m' k' :=
  match t with
  | var x => var (ρ.var x)
  | lam t1 t2 => lam (t1.rename ρ) (t2.rename ρ.ext)
  | tlam t1 t2 => tlam (t1.rename ρ) (t2.rename ρ.text)
  | clam k t => clam k (t.rename ρ.cext)
  | pack x y => pack (ρ.cvar x) (ρ.var y)
  | app x y => app (ρ.var x) (ρ.var y)
  | tapp x X => tapp (ρ.var x) (ρ.tvar X)
  | capp x c => capp (ρ.var x) (ρ.cvar c)
  | letin t1 t2 => letin (t1.rename ρ) (t2.rename ρ.ext)
  | unpack t1 t2 => unpack (t1.rename ρ) (t2.rename ρ.cext.ext)
  | bindc C t => bindc (C.rename ρ) (t.rename ρ.cext)
  | bindt T t => bindt (T.rename ρ) (t.rename ρ.text)

end Capybara
