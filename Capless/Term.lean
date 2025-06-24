import Capless.CaptureSet
import Capless.Type
import Capless.Basic
namespace Capless

/-!
# Terms in System Capless

This module defines the syntax of terms (Fig. 1) in System Capless.

## Intrinsically-Scoped Syntax

The terms are deBruijn-indexed and intrinsically-scoped. The type `Term` is parameterized by three natural numbers representing the number of available binders in each category:
- `n`: number of term variables
- `m`: number of type variables
- `k`: number of capture variables

A binder reference is always valid and represented as a `Fin` index, ensuring well-formedness by construction.

## Full Monadic Normal Form

The system defined in the paper applies monadic normal form (MNF) to terms. Deviating from the paper, this mechanization applies MNF to types and captures as well. As demonstrated in `Term.tapp` and `Term.capp`, type and capture applications only accept type and capture variables as arguments, respectively.

Full expressiveness is recovered through the `Term.bindt` and `Term.bindc` binding forms, which bind concrete types and capture sets as type and capture variables. For example, a term `x[{y,z}]` can be equivalently represented in full-MNF as:

```lean
let c = {y,z} in
  x[c]
```

Such a formalization largely simplifies the metatheory: the only term and type transformation is needed is renaming (i.e. substituting a index for another index). By contrast, the original definition on the paper requires substitution for types and captures (i.e. substituting a type/capture variable index for a concrete type/capture-set).

## Main Definitions
-/

/-- A `Term n m k` is a Capless term in a context with `n` term variables, `m` type variables, and `k` capture variables. -/
inductive Term : Nat -> Nat -> Nat -> Type where
/-- Variable `x`. -/
| var : Fin n -> Term n m k
/-- Term lambda `λ(x: T)t`. -/
| lam : CType n m k -> Term (n+1) m k -> Term n m k
/-- Type lambda `λ[X<:S]t`. -/
| tlam : SType n m k -> Term n (m+1) k -> Term n m k
/-- Capture lambda `λ[c<:B]t`. -/
| clam : CBound n k -> Term n m (k+1) -> Term n m k
/-- Packed term `<c,x>`. -/
| pack : CaptureSet n k -> Fin n -> Term n m k
/-- Application `x y`. -/
| app : Fin n -> Fin n -> Term n m k
/-- Application `x y` for capabilities. -/
| invoke : Fin n -> Fin n -> Term n m k
/-- Type application `x[X]`. -/
| tapp : Fin n -> Fin m -> Term n m k
/-- Capture application `x[c]`. -/
| capp : Fin n -> Fin k -> Term n m k
/-- Let `let x = t in u`. -/
| letin : Term n m k -> Term (n+1) m k -> Term n m k
/-- Existential-let `let <c,x> = t in u`. -/
| letex : Term n m k -> Term (n+1) m (k+1) -> Term n m k
/-- Type binding. -/
| bindt : SType n m k -> Term n (m+1) k -> Term n m k
/-- Capture binding. -/
| bindc : CaptureSet n k -> Term n m (k+1) -> Term n m k
/-- Boundary form `boundary[S] as <c,x> in t`. -/
| boundary : SType n m k -> Term (n+1) m (k+1) -> Term n m k

/-!
## Notations
-/

notation:50 "λ(x:" T ")" t => Term.lam T t
notation:50 "λ[X<:" S "]" t => Term.tlam S t
notation:50 "λ[c<:" B "]" t => Term.clam B t
notation:40 "let" "x=" t " in " u => Term.letin t u
notation:40 "let" "(c,x)=" t " in " u => Term.letex t u
notation:40 "let" "X=" S " in " t => Term.bindt S t
notation:40 "let" "c=" C " in " t => Term.bindc C t
notation:40 "boundary:" S " in " t => Term.boundary S t

/-- Whether this term is a value? -/
@[aesop safe constructors]
inductive Term.IsValue : Term n m k -> Prop where
| lam : Term.IsValue (lam E t)
| tlam : Term.IsValue (tlam S t)
| clam : Term.IsValue (clam B t)
| pack : Term.IsValue (pack c x)

/-!
## Renaming Operations on `Term`
-/


def Term.rename (t : Term n m k) (f : FinFun n n') : Term n' m k :=
  match t with
  | Term.var x => Term.var (f x)
  | Term.lam E t => Term.lam (E.rename f) (t.rename f.ext)
  | Term.tlam S t => Term.tlam (S.rename f) (t.rename f)
  | Term.clam B t => Term.clam (B.rename f) (t.rename f)
  | Term.pack C x => Term.pack (C.rename f) (f x)
  | Term.app x y => Term.app (f x) (f y)
  | Term.invoke x y => Term.invoke (f x) (f y)
  | Term.tapp x X => Term.tapp (f x) X
  | Term.capp x c => Term.capp (f x) c
  | Term.letin t u => Term.letin (t.rename f) (u.rename f.ext)
  | Term.letex t u => Term.letex (t.rename f) (u.rename f.ext)
  | Term.bindt S t => Term.bindt (S.rename f) (t.rename f)
  | Term.bindc c t => Term.bindc (c.rename f) (t.rename f)
  | Term.boundary S t => Term.boundary (S.rename f) (t.rename f.ext)

def Term.trename (t : Term n m k) (f : FinFun m m') : Term n m' k :=
  match t with
  | Term.var x => Term.var x
  | Term.lam E t => Term.lam (E.trename f) (t.trename f)
  | Term.tlam S t => Term.tlam (S.trename f) (t.trename f.ext)
  | Term.clam B t => Term.clam B (t.trename f)
  | Term.pack c x => Term.pack c x
  | Term.app x y => Term.app x y
  | Term.invoke x y => Term.invoke x y
  | Term.tapp x X => Term.tapp x (f X)
  | Term.capp x c => Term.capp x c
  | Term.letin t u => Term.letin (t.trename f) (u.trename f)
  | Term.letex t u => Term.letex (t.trename f) (u.trename f)
  | Term.bindt S t => Term.bindt (S.trename f) (t.trename f.ext)
  | Term.bindc c t => Term.bindc c (t.trename f)
  | Term.boundary S t => Term.boundary (S.trename f) (t.trename f)

def Term.crename (t : Term n m k) (f : FinFun k k') : Term n m k' :=
  match t with
  | Term.var x => Term.var x
  | Term.lam E t => Term.lam (E.crename f) (t.crename f)
  | Term.tlam S t => Term.tlam (S.crename f) (t.crename f)
  | Term.clam B t => Term.clam (B.crename f) (t.crename f.ext)
  | Term.pack C x => Term.pack (C.crename f) x
  | Term.app x y => Term.app x y
  | Term.invoke x y => Term.invoke x y
  | Term.tapp x X => Term.tapp x X
  | Term.capp x c => Term.capp x (f c)
  | Term.letin t u => Term.letin (t.crename f) (u.crename f)
  | Term.letex t u => Term.letex (t.crename f) (u.crename f.ext)
  | Term.bindt S t => Term.bindt (S.crename f) (t.crename f)
  | Term.bindc c t => Term.bindc (c.crename f) (t.crename f.ext)
  | Term.boundary S t => Term.boundary (S.crename f) (t.crename f.ext)

def Term.weaken (t : Term n m k) : Term (n+1) m k := t.rename FinFun.weaken

def Term.weaken1 (t : Term (n+1) m k) : Term (n+2) m k :=
  t.rename FinFun.weaken.ext

def Term.tweaken (t : Term n m k) : Term n (m+1) k := t.trename FinFun.weaken

def Term.cweaken (t : Term n m k) : Term n m (k+1) := t.crename FinFun.weaken

def Term.cweaken1 (t : Term n m (k+1)) : Term n m (k+2) :=
  t.crename FinFun.weaken.ext

def Term.open (t : Term (n+1) m k) (x : Fin n) : Term n m k :=
  t.rename (FinFun.open x)

def Term.topen (t : Term n (m+1) k) (X : Fin m) : Term n m k :=
  t.trename (FinFun.open X)

def Term.copen (t : Term n m (k+1)) (c : Fin k) : Term n m k :=
  t.crename (FinFun.open c)

/-!
## Basic Properties
-/

theorem IsValue.rename_l' {t : Term n m k} {t0 : Term n' m k}
  (he : t0 = t.rename f)
  (hv : t0.IsValue) :
  t.IsValue := by
  cases hv
  all_goals (cases t <;> simp [Term.rename] at he; try constructor)

theorem IsValue.rename_l {t : Term n m k}
  (hv : (t.rename f).IsValue) :
  t.IsValue := IsValue.rename_l' rfl hv

theorem IsValue.crename_l' {t : Term n m k} {t0 : Term n m k'}
  (he : t0 = t.crename f)
  (hv : t0.IsValue) :
  t.IsValue := by
  cases hv
  all_goals (cases t <;> simp [Term.crename] at he; try constructor)

theorem IsValue.crename_l {t : Term n m k}
  (hv : (t.crename f).IsValue) :
  t.IsValue := IsValue.crename_l' rfl hv

theorem IsValue.trename_l' {t : Term n m k} {t0 : Term n m' k}
  (he : t0 = t.trename f)
  (hv : t0.IsValue) :
  t.IsValue := by
  cases hv
  all_goals (cases t <;> simp [Term.trename] at he; try constructor)

theorem IsValue.trename_l {t : Term n m k}
  (hv : (t.trename f).IsValue) :
  t.IsValue := IsValue.trename_l' rfl hv

theorem IsValue.rename_r {t : Term n m k}
  (hv : t.IsValue) :
  (t.rename f).IsValue := by
  cases hv <;> simp [Term.rename] <;> constructor

theorem IsValue.trename_r {t : Term n m k}
  (hv : t.IsValue) :
  (t.trename f).IsValue := by
  cases hv <;> simp [Term.trename] <;> constructor

theorem IsValue.crename_r {t : Term n m k}
  (hv : t.IsValue) :
  (t.crename f).IsValue := by
  cases hv <;> simp [Term.crename] <;> constructor


theorem Term.rename_id {t : Term n m k} :
  t.rename FinFun.id = t := by
  induction t
  case var => simp [Term.rename, FinFun.id]
  case lam =>
    simp [Term.rename, CType.rename_id, FinFun.id_ext]
    trivial
  case tlam =>
    simp [Term.rename, SType.rename_id]
    trivial
  case clam =>
    simp [Term.rename, CBound.rename_id]
    trivial
  case pack =>
    simp [Term.rename, CaptureSet.rename_id, FinFun.id]
  case app =>
    simp [Term.rename, FinFun.id]
  case invoke =>
    simp [Term.rename, FinFun.id]
  case tapp =>
    simp [Term.rename, FinFun.id]
  case capp =>
    simp [Term.rename, FinFun.id]
  case letin ih1 ih2 =>
    simp [Term.rename, FinFun.id_ext, ih1, ih2]
  case letex ih1 ih2 =>
    simp [Term.rename, FinFun.id_ext, ih1, ih2]
  case bindt ih =>
    simp [Term.rename, SType.rename_id, ih]
  case bindc ih =>
    simp [Term.rename, CaptureSet.rename_id, ih]
  case boundary ih =>
    simp [Term.rename, SType.rename_id, ih, FinFun.id_ext]

theorem Term.trename_id {t : Term n m k} :
  t.trename FinFun.id = t := by
  induction t
  case var =>
    simp [Term.trename]
  case lam ih =>
    simp [Term.trename, CType.trename_id]
    exact ih
  case tlam ih =>
    simp [Term.trename, SType.trename_id, FinFun.id_ext]
    exact ih
  case clam ih =>
    simp [Term.trename]
    exact ih
  case pack =>
    simp [Term.trename]
  case app =>
    simp [Term.trename]
  case invoke =>
    simp [Term.trename]
  case tapp =>
    simp [Term.trename, FinFun.id]
  case capp =>
    simp [Term.trename]
  case letin ih1 ih2 =>
    simp [Term.trename, ih1, ih2]
  case letex ih1 ih2 =>
    simp [Term.trename, ih1, ih2]
  case bindt ih =>
    simp [Term.trename, SType.trename_id, FinFun.id_ext]
    exact ih
  case bindc ih =>
    simp [Term.trename]
    exact ih
  case boundary ih =>
    simp [Term.trename, SType.trename_id, ih, FinFun.id_ext]

theorem Term.crename_id {t : Term n m k} :
  t.crename FinFun.id = t := by
  induction t
  case var =>
    simp [Term.crename]
  case lam ih =>
    simp [Term.crename]
    simp [ih, CType.crename_id]
  case tlam ih =>
    simp [Term.crename]
    simp [ih, SType.crename_id]
  case clam ih =>
    simp [Term.crename, ih, CBound.crename_id, FinFun.id_ext]
  case pack =>
    simp [Term.crename, CaptureSet.crename_id]
  case app =>
    simp [Term.crename]
  case invoke =>
    simp [Term.crename]
  case tapp =>
    simp [Term.crename]
  case capp =>
    simp [Term.crename, FinFun.id]
  case letin ih1 ih2 =>
    simp [Term.crename, ih1, ih2]
  case letex ih1 ih2 =>
    simp [Term.crename, ih1, ih2, FinFun.id_ext]
  case bindt ih =>
    simp [Term.crename]
    simp [ih, SType.crename_id]
  case bindc ih =>
    simp [Term.crename]
    simp [CaptureSet.crename_id, FinFun.id_ext, ih]
  case boundary ih =>
    simp [Term.crename]
    simp [ih, SType.crename_id, FinFun.id_ext]

theorem Term.rename_rename {t : Term n m k} {f : FinFun n n'} {g : FinFun n' n''} :
  (t.rename f).rename g = t.rename (g.comp f) := by
  induction t generalizing g n' n''
  case var => simp [rename]
  case lam ih =>
    simp [rename, CType.rename_rename]
    simp [<- FinFun.ext_comp_ext, ih]
  case tlam ih =>
    simp [rename, SType.rename_rename]
    simp [<- FinFun.ext_comp_ext, ih]
  case clam ih =>
    simp [rename]
    simp [<- FinFun.ext_comp_ext, ih, CBound.rename_rename]
  case pack =>
    simp [rename, CaptureSet.rename_rename]
  case app =>
    simp [rename]
  case invoke =>
    simp [rename]
  case tapp =>
    simp [rename]
  case capp =>
    simp [rename]
  case letin ih1 ih2 =>
    simp [rename]
    simp [<- FinFun.ext_comp_ext, ih1, ih2]
  case letex ih1 ih2 =>
    simp [rename]
    simp [<- FinFun.ext_comp_ext, ih1, ih2]
  case bindt ih =>
    simp [rename, SType.rename_rename]
    simp [<- FinFun.ext_comp_ext, ih]
  case bindc ih =>
    simp [rename, CaptureSet.rename_rename]
    simp [<- FinFun.ext_comp_ext, ih]
  case boundary ih =>
    simp [rename, SType.rename_rename]
    simp [<- FinFun.ext_comp_ext, ih]

theorem Term.crename_crename {t : Term n m k} {f : FinFun k k'} {g : FinFun k' k''} :
  (t.crename f).crename g = t.crename (g.comp f) := by
  induction t generalizing g k' k''
  case var => simp [crename]
  case lam ih =>
    simp [crename, CType.crename_crename]
    simp [<- FinFun.ext_comp_ext, ih]
  case tlam ih =>
    simp [crename, SType.crename_crename]
    simp [<- FinFun.ext_comp_ext, ih]
  case clam ih =>
    simp [crename]
    simp [<- FinFun.ext_comp_ext, ih, CBound.crename_crename]
  case pack =>
    simp [crename, CaptureSet.crename_crename]
  case app =>
    simp [crename]
  case invoke =>
    simp [crename]
  case tapp =>
    simp [crename]
  case capp =>
    simp [crename]
  case letin ih1 ih2 =>
    simp [crename]
    simp [<- FinFun.ext_comp_ext, ih1, ih2]
  case letex ih1 ih2 =>
    simp [crename]
    simp [<- FinFun.ext_comp_ext, ih1, ih2]
  case bindt ih =>
    simp [crename, SType.crename_crename]
    simp [<- FinFun.ext_comp_ext, ih]
  case bindc ih =>
    simp [crename, CaptureSet.crename_crename]
    simp [<- FinFun.ext_comp_ext, ih]
  case boundary ih =>
    simp [crename, SType.crename_crename]
    simp [<- FinFun.ext_comp_ext, ih]

theorem Term.trename_trename {t : Term n m k} {f : FinFun m m'} {g : FinFun m' m''} :
  (t.trename f).trename g = t.trename (g.comp f) := by
  induction t generalizing g m' m''
  case var => simp [trename]
  case lam ih =>
    simp [trename, CType.trename_trename]
    simp [<- FinFun.ext_comp_ext, ih]
  case tlam ih =>
    simp [trename, SType.trename_trename]
    simp [<- FinFun.ext_comp_ext, ih]
  case clam ih =>
    simp [trename]
    simp [<- FinFun.ext_comp_ext, ih]
  case pack =>
    simp [trename]
  case app =>
    simp [trename]
  case invoke =>
    simp [trename]
  case tapp =>
    simp [trename]
  case capp =>
    simp [trename]
  case letin ih1 ih2 =>
    simp [trename]
    simp [<- FinFun.ext_comp_ext, ih1, ih2]
  case letex ih1 ih2 =>
    simp [trename]
    simp [<- FinFun.ext_comp_ext, ih1, ih2]
  case bindt ih =>
    simp [trename, SType.trename_trename]
    simp [<- FinFun.ext_comp_ext, ih]
  case bindc ih =>
    simp [trename]
    simp [<- FinFun.ext_comp_ext, ih]
  case boundary ih =>
    simp [trename, SType.trename_trename]
    simp [<- FinFun.ext_comp_ext, ih]

end Capless
