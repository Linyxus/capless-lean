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

def Renaming.id : Renaming n m k n m k :=
  {
    var := FinFun.id
    tvar := FinFun.id
    cvar := FinFun.id
  }

def FinFun.comp (f : FinFun n n') (g : FinFun n' n'') : FinFun n n'' :=
  fun x => g (f x)

def Renaming.comp (ρ : Renaming n m k n' m' k') (ρ' : Renaming n' m' k' n'' m'' k'') : Renaming n m k n'' m'' k'' :=
  {
    var := ρ.var.comp ρ'.var
    tvar := ρ.tvar.comp ρ'.tvar
    cvar := ρ.cvar.comp ρ'.cvar
  }

/-!
Basic properties of renamings.
-/
theorem Renaming.ext_var_zero {ρ : Renaming n m k n' m' k'} : ρ.ext.var 0 = 0 := by
  simp [Renaming.ext]
  rfl

theorem Renaming.ext_var_succ {ρ : Renaming n m k n' m' k'} {x : Fin n} : ρ.ext.var (Fin.succ x) = Fin.succ (ρ.var x) := by
  simp [Renaming.ext]
  rfl

theorem FinFun.id_comp_id {n : Nat} : FinFun.comp (n:=n) FinFun.id FinFun.id = FinFun.id := by rfl

theorem Renaming.id_comp_id {n m k : Nat} : Renaming.comp (n:=n) (m:=m) (k:=k) Renaming.id Renaming.id = Renaming.id := by rfl

theorem FinFun.id_ext {n : Nat} : FinFun.ext (n:=n) FinFun.id = FinFun.id := by
  funext x0
  cases x0 using Fin.cases
  case zero => simp [FinFun.id, FinFun.ext]
  case succ x0 => simp [FinFun.id, FinFun.ext]

theorem Renaming.id_ext {n m k : Nat} : Renaming.ext (n:=n) (m:=m) (k:=k) Renaming.id = Renaming.id := by simp [Renaming.ext, Renaming.id, FinFun.id_ext]

theorem Renaming.id_text {n m k : Nat} : Renaming.text (n:=n) (m:=m) (k:=k) Renaming.id = Renaming.id := by simp [Renaming.text, Renaming.id, FinFun.id_ext]

theorem Renaming.id_cext {n m k : Nat} : Renaming.cext (n:=n) (m:=m) (k:=k) Renaming.id = Renaming.id := by simp [Renaming.cext, Renaming.id, FinFun.id_ext]

theorem FinFun.comp_ext {f : FinFun n n'} {g : FinFun n' n''} : (f.comp g).ext = f.ext.comp g.ext := by
  funext x
  cases x using Fin.cases
  case zero => rfl
  case succ x0 => simp [FinFun.comp, FinFun.ext]

theorem Renaming.comp_ext {ρ : Renaming n m k n' m' k'} {ρ' : Renaming n' m' k' n'' m'' k''} :
  (ρ.comp ρ').ext = ρ.ext.comp ρ'.ext := by
  simp [Renaming.ext, Renaming.comp, FinFun.comp_ext]

theorem Renaming.comp_text {ρ : Renaming n m k n' m' k'} {ρ' : Renaming n' m' k' n'' m'' k''} :
  (ρ.comp ρ').text = ρ.text.comp ρ'.text := by
  simp [Renaming.text, Renaming.comp, FinFun.comp_ext]

theorem Renaming.comp_cext {ρ : Renaming n m k n' m' k'} {ρ' : Renaming n' m' k' n'' m'' k''} :
  (ρ.comp ρ').cext = ρ.cext.comp ρ'.cext := by
  simp [Renaming.cext, Renaming.comp, FinFun.comp_ext]

theorem FinFun.comp_weaken {f : FinFun n n'} :
  f.comp FinFun.weaken = FinFun.weaken.comp (f.ext) := by
  funext x
  simp [FinFun.comp, FinFun.weaken, FinFun.ext]

theorem FinFun.comp_id {f : FinFun n n'} : f.comp FinFun.id = f := by
  funext x
  simp [FinFun.comp, FinFun.id]

theorem FinFun.id_comp {f : FinFun n n'} : FinFun.id.comp f = f := by
  funext x
  simp [FinFun.comp, FinFun.id]

theorem Renaming.comp_weaken {ρ : Renaming n m k n' m' k'} :
  ρ.comp Renaming.weaken = Renaming.weaken.comp ρ.ext := by
  simp [Renaming.weaken, Renaming.comp, Renaming.ext]
  simp [FinFun.comp_weaken, FinFun.comp_id, FinFun.id_comp]

theorem Renaming.comp_tweaken {ρ : Renaming n m k n' m' k'} :
  ρ.comp Renaming.tweaken = Renaming.tweaken.comp ρ.text := by
  simp [Renaming.tweaken, Renaming.comp, Renaming.text]
  simp [FinFun.comp_weaken, FinFun.comp_id, FinFun.id_comp]

theorem Renaming.comp_cweaken {ρ : Renaming n m k n' m' k'} :
  ρ.comp Renaming.cweaken = Renaming.cweaken.comp ρ.cext := by
  simp [Renaming.cweaken, Renaming.comp, Renaming.cext]
  simp [FinFun.comp_weaken, FinFun.comp_id, FinFun.id_comp]

end Capybara
