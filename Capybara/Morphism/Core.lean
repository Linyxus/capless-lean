import Mathlib.Data.Fin.Basic
namespace Capybara
/-!
# Morphisms

This module defines morphisms between contexts in the Capybara type system.

## Main definitions

- `FinFun n n'`: A function mapping finite indices from dimension `n` to dimension `n'`
- `Renaming n m k n' m' k'`: A renaming morphism that maps between contexts with dimensions:
  - `n` term variables to `n'` term variables
  - `m` type variables to `m'` type variables
  - `k` capture set variables to `k'` capture set variables

## Implementation Notes

Renamings are used to implement variable substitution and weakening in a well-typed way.
The three dimensions (term, type, and capture set variables) are handled separately but
in parallel through the `Renaming` structure.

Each dimension can be extended independently through the `ext`, `text` and `cext` operations
which add a new variable while preserving the existing mapping.

note: Sonnet wrote this documentation.
-/

/-!
A renaming function maps indices from one dimension to another.
-/
def FinFun (n : Nat) (n' : Nat) : Type := Fin n -> Fin n'

/-!
Extend a renaming function by one on the term variable dimension.
-/
def FinFun.ext (f : FinFun n n') : FinFun (n+1) (n'+1) := by
  intro x
  cases x using Fin.cases
  case zero => exact 0
  case succ x0 => exact Fin.succ (f x0)

def FinFun.id {n : Nat} : FinFun n n := fun x => x

/-!
A weaken function that shifts all indices by one.
-/
def FinFun.weaken {n : Nat} : FinFun n (n+1) := by
  intro x
  exact Fin.succ x

/-!
Open a bound variable.
-/
def FinFun.open {n : Nat} (x : Fin n) : FinFun (n+1) n := by
  intro y
  cases y using Fin.cases
  case zero => exact x
  case succ y0 => exact y0

/-!
A renaming function, which maps the three dimensions of a context (term, type, and capture set variables).
-/
structure Renaming (n m k n' m' k' : Nat) where
  var : FinFun n n'
  tvar : FinFun m m'
  cvar : FinFun k k'

/-!
Extend a renaming function by one on the term variable dimension.
-/
def Renaming.ext (ρ : Renaming n m k n' m' k') :
  Renaming (n+1) m k (n'+1) m' k' :=
  {
    var := ρ.var.ext
    tvar := ρ.tvar
    cvar := ρ.cvar
  }

/-!
Extend a renaming function by one on the type variable dimension.
-/
def Renaming.text (ρ : Renaming n m k n' m' k') :
  Renaming n (m+1) k n' (m'+1) k' :=
  {
    var := ρ.var
    tvar := ρ.tvar.ext
    cvar := ρ.cvar
  }

/-!
Extend a renaming function by one on the capture set variable dimension.
-/
def Renaming.cext (ρ : Renaming n m k n' m' k') :
  Renaming n m (k+1) n' m' (k'+1) :=
  {
    var := ρ.var
    tvar := ρ.tvar
    cvar := ρ.cvar.ext
  }

/-!
Weaken the renaming by one on the term variable dimension.
-/
def Renaming.weaken : Renaming n m k (n+1) m k :=
  {
    var := FinFun.weaken
    tvar := FinFun.id
    cvar := FinFun.id
  }

/-!
Weaken the renaming by one on the type variable dimension.
-/
def Renaming.tweaken : Renaming n m k n (m+1) k :=
  {
    var := FinFun.id
    tvar := FinFun.weaken
    cvar := FinFun.id
  }

/-!
Weaken the renaming by one on the capture variable dimension.
-/
def Renaming.cweaken : Renaming n m k n m (k+1) :=
  {
    var := FinFun.id
    tvar := FinFun.id
    cvar := FinFun.weaken
  }

def Renaming.open (x : Fin n) : Renaming (n+1) m k n m k :=
  {
    var := FinFun.open x
    tvar := FinFun.id
    cvar := FinFun.id
  }

def Renaming.topen (X : Fin m) : Renaming n (m+1) k n m k :=
  {
    var := FinFun.id
    tvar := FinFun.open X
    cvar := FinFun.id
  }

def Renaming.copen (X : Fin k) : Renaming n m (k+1) n m k :=
  {
    var := FinFun.id
    tvar := FinFun.id
    cvar := FinFun.open X
  }

end Capybara
