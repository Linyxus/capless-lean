import Capybara.Syntax.Type
namespace Capybara
/-!
# Term Syntax

This module defines the syntax of terms in the Capybara language.

## Main Definitions

- `Term n m k`: Terms with `n` term variables, `m` type variables, and `k` capture set variables
- `Term.rename`: Renaming operation for terms

## Term Constructors

- Variables: `var`
- Functions: `lam` (term abstraction), `tlam` (type abstraction), `clam` (capture abstraction), `flam` (fresh capture abstraction)
- Applications: `app` (term application), `tapp` (type application), `capp` (capture set application)
- Capture set operations: `pack` (capture set creation), `unpack` (capture set elimination)
- Let bindings: `letin` (term binding)
- Aliases: `calias` (capture set alias), `talias` (type alias)

The indices `n`, `m`, and `k` track the number of term variables, type variables, and capture set variables
in scope, respectively. This ensures well-scopedness of terms through the type system.
-/

/-!
Term definitions.
-/
inductive Term : Nat -> Nat -> Nat -> Type where
| var : Fin n -> Term n m k
| lam : CType n m k -> Term (n+1) m k -> Term n m k
| tlam : SType n m k -> Term n (m+1) k -> Term n m k
| clam : SepDegree n k -> Term n m (k+1) -> Term n m k
| flam : CType n m (k+1) -> Term (n+1) m (k+1) -> Term n m k
| pack : Fin k -> Fin n -> Term n m k
| app : Fin n -> Fin n -> Term n m k
| tapp : Fin n -> Fin m -> Term n m k
| capp : Fin n -> Fin k -> Term n m k
| fapp : Fin n -> Fin k -> Fin n -> Term n m k
| letin : Term n m k -> Term (n+1) m k -> Term n m k
| unpack : Term n m k -> Term (n+1) m (k+1) -> Term n m k
| calias : CaptureSet n k -> Term n m (k+1) -> Term n m k
| talias : SType n m k -> Term n (m+1) k -> Term n m k

/-!
Renaming operation for terms.
-/
def Term.rename
  (t : Term n m k)
  (ρ : Renaming n m k n' m' k') :
  Term n' m' k' :=
  match t with
  | var x => var (ρ.var x)
  | lam t1 t2 => lam (t1.rename ρ) (t2.rename ρ.ext)
  | tlam t1 t2 => tlam (t1.rename ρ) (t2.rename ρ.text)
  | clam D t => clam (D.rename ρ) (t.rename ρ.cext)
  | flam T t => flam (T.rename ρ.cext) (t.rename ρ.cext.ext)
  | pack x y => pack (ρ.cvar x) (ρ.var y)
  | app x y => app (ρ.var x) (ρ.var y)
  | tapp x X => tapp (ρ.var x) (ρ.tvar X)
  | capp x c => capp (ρ.var x) (ρ.cvar c)
  | fapp x c y => fapp (ρ.var x) (ρ.cvar c) (ρ.var y)
  | letin t1 t2 => letin (t1.rename ρ) (t2.rename ρ.ext)
  | unpack t1 t2 => unpack (t1.rename ρ) (t2.rename ρ.cext.ext)
  | calias C t => calias (C.rename ρ) (t.rename ρ.cext)
  | talias T t => talias (T.rename ρ) (t.rename ρ.text)

/-!
Weakening operation for terms.
-/
def Term.weaken : Term n m k -> Term (n+1) m k :=
  fun t => t.rename Renaming.weaken
def Term.tweaken : Term n m k -> Term n (m+1) k :=
  fun t => t.rename Renaming.tweaken
def Term.cweaken : Term n m k -> Term n m (k+1) :=
  fun t => t.rename Renaming.cweaken

end Capybara
