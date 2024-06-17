import Capless.CaptureSet
import Capless.Type
import Capless.Basic
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

def Term.rename (t : Term n m k) (f : FinFun n n') : Term n' m k :=
  match t with
  | Term.var x => Term.var (f x)
  | Term.lam E t => Term.lam (E.rename f) (t.rename f.ext)
  | Term.tlam S t => Term.tlam (S.rename f) (t.rename f)
  | Term.clam t => Term.clam (t.rename f)
  | Term.boxed x => Term.boxed (f x)
  | Term.pack c x => Term.pack c (f x)
  | Term.app x y => Term.app (f x) (f y)
  | Term.tapp x X => Term.tapp (f x) X
  | Term.capp x c => Term.capp (f x) c
  | Term.letin t u => Term.letin (t.rename f) (u.rename f.ext)
  | Term.bindt S t => Term.bindt (S.rename f) (t.rename f)
  | Term.bindc c t => Term.bindc (c.rename f) (t.rename f)
  | Term.unbox c x => Term.unbox (c.rename f) (f x)

def Term.trename (t : Term n m k) (f : FinFun m m') : Term n m' k :=
  match t with
  | Term.var x => Term.var x
  | Term.lam E t => Term.lam (E.trename f) (t.trename f)
  | Term.tlam S t => Term.tlam (S.trename f) (t.trename f.ext)
  | Term.clam t => Term.clam (t.trename f)
  | Term.boxed x => Term.boxed x
  | Term.pack c x => Term.pack c x
  | Term.app x y => Term.app x y
  | Term.tapp x X => Term.tapp x (f X)
  | Term.capp x c => Term.capp x c
  | Term.letin t u => Term.letin (t.trename f) (u.trename f)
  | Term.bindt S t => Term.bindt (S.trename f) (t.trename f.ext)
  | Term.bindc c t => Term.bindc c (t.trename f)
  | Term.unbox c x => Term.unbox c x

def Term.crename (t : Term n m k) (f : FinFun k k') : Term n m k' :=
  match t with
  | Term.var x => Term.var x
  | Term.lam E t => Term.lam (E.crename f) (t.crename f)
  | Term.tlam S t => Term.tlam (S.crename f) (t.crename f)
  | Term.clam t => Term.clam (t.crename f.ext)
  | Term.boxed x => Term.boxed x
  | Term.pack c x => Term.pack (f c) x
  | Term.app x y => Term.app x y
  | Term.tapp x X => Term.tapp x X
  | Term.capp x c => Term.capp x (f c)
  | Term.letin t u => Term.letin (t.crename f) (u.crename f)
  | Term.bindt S t => Term.bindt (S.crename f) (t.crename f)
  | Term.bindc c t => Term.bindc (c.crename f) (t.crename f.ext)
  | Term.unbox c x => Term.unbox (c.crename f) x

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

def Term.weaken (t : Term n m k) : Term (n+1) m k := t.rename FinFun.weaken

def Term.tweaken (t : Term n m k) : Term n (m+1) k := t.trename FinFun.weaken

def Term.cweaken (t : Term n m k) : Term n m (k+1) := t.crename FinFun.weaken

def Term.open (t : Term (n+1) m k) (x : Fin n) : Term n m k :=
  t.rename (FinFun.open x)

def Term.topen (t : Term n (m+1) k) (X : Fin m) : Term n m k :=
  t.trename (FinFun.open X)

def Term.copen (t : Term n m (k+1)) (c : Fin k) : Term n m k :=
  t.crename (FinFun.open c)

end Capless
