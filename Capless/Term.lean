import Capless.CaptureSet
import Capless.Type
import Capless.Basic
namespace Capless

inductive Term : Nat -> Nat -> Nat -> Type where
| var : Fin n -> Term n m k
| lam : CType n m k -> Term (n+1) m k -> Term n m k
| tlam : SType n m k -> Term n (m+1) k -> Term n m k
| clam : Term n m (k+1) -> Term n m k
| boxed : Fin n -> Term n m k
| pack : CaptureSet n k -> Fin n -> Term n m k
| app : Fin n -> Fin n -> Term n m k
| tapp : Fin n -> Fin m -> Term n m k
| capp : Fin n -> Fin k -> Term n m k
| letin : Term n m k -> Term (n+1) m k -> Term n m k
| letex : Term n m k -> Term (n+1) m (k+1) -> Term n m k
| bindt : SType n m k -> Term n (m+1) k -> Term n m k
| bindc : CaptureSet n k -> Term n m (k+1) -> Term n m k
| unbox : CaptureSet n k -> Fin n -> Term n m k

notation:50 "λ(x:" T ")" t => Term.lam T t
notation:50 "λ[X<:" S "]" t => Term.tlam S t
notation:50 "λ[c]" t => Term.clam t
notation:50 C " o- " x => Term.unbox C x
notation:40 "let x=" t "in" u => Term.letin t u
notation:40 "let (c,x)=" t "in" u => Term.letex t u
notation:40 "let X=" S "in" t => Term.bindt S t
notation:40 "let c=" C "in" t => Term.bindc C t

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
  | Term.pack C x => Term.pack (C.rename f) (f x)
  | Term.app x y => Term.app (f x) (f y)
  | Term.tapp x X => Term.tapp (f x) X
  | Term.capp x c => Term.capp (f x) c
  | Term.letin t u => Term.letin (t.rename f) (u.rename f.ext)
  | Term.letex t u => Term.letex (t.rename f) (u.rename f.ext)
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
  | Term.letex t u => Term.letex (t.trename f) (u.trename f)
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
  | Term.pack C x => Term.pack (C.crename f) x
  | Term.app x y => Term.app x y
  | Term.tapp x X => Term.tapp x X
  | Term.capp x c => Term.capp x (f c)
  | Term.letin t u => Term.letin (t.crename f) (u.crename f)
  | Term.letex t u => Term.letex (t.crename f) (u.crename f.ext)
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
    simp [Term.rename, SType.rename_id]
    trivial
  case boxed =>
    simp [Term.rename, FinFun.id]
  case unbox =>
    simp [Term.rename, CaptureSet.rename_id, FinFun.id]
  case pack =>
    simp [Term.rename, CaptureSet.rename_id, FinFun.id]
  case app =>
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
  case boxed =>
    simp [Term.trename]
  case pack =>
    simp [Term.trename]
  case app =>
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
  case unbox =>
    simp [Term.trename]

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
    simp [Term.crename, ih, FinFun.id_ext]
  case boxed =>
    simp [Term.crename]
  case pack =>
    simp [Term.crename, CaptureSet.crename_id]
  case app =>
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
  case unbox =>
    simp [Term.crename, CaptureSet.crename_id]

end Capless
