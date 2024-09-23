import Capless.CaptureSet
import Capless.Basic
import Capless.Type.Core
namespace Capless

mutual

def EType.rename : EType n m k -> FinFun n n' -> EType n' m k
| EType.ex T, f => EType.ex (T.rename f)
| EType.type T, f => EType.type (T.rename f)

def CType.rename : CType n m k -> FinFun n n' -> CType n' m k
| CType.capt C S, f => CType.capt (C.rename f) (S.rename f)

def SType.rename : SType n m k -> FinFun n n' -> SType n' m k
| SType.top, _ => SType.top
| SType.tvar X, _ => SType.tvar X
| SType.forall E1 E2, f => SType.forall (E1.rename f) (E2.rename f.ext)
| SType.tforall S E, f => SType.tforall (S.rename f) (E.rename f)
| SType.cforall E, f => SType.cforall (E.rename f)
| SType.box T, f => SType.box (T.rename f)

end

mutual

def EType.trename : EType n m k -> FinFun m m' -> EType n m' k
| EType.ex T, f => EType.ex (T.trename f)
| EType.type T, f => EType.type (T.trename f)

def CType.trename : CType n m k -> FinFun m m' -> CType n m' k
| CType.capt C S, f => CType.capt C (S.trename f)

def SType.trename : SType n m k -> FinFun m m' -> SType n m' k
| SType.top, _ => SType.top
| SType.tvar X, f => SType.tvar (f X)
| SType.forall E1 E2, f => SType.forall (E1.trename f) (E2.trename f)
| SType.tforall S E, f => SType.tforall (S.trename f) (E.trename f.ext)
| SType.cforall E, f => SType.cforall (E.trename f)
| SType.box T, f => SType.box (T.trename f)

end

mutual

def EType.crename : EType n m k -> FinFun k k' -> EType n m k'
| EType.ex T, f => EType.ex (T.crename f.ext)
| EType.type T, f => EType.type (T.crename f)

def CType.crename : CType n m k -> FinFun k k' -> CType n m k'
| CType.capt C S, f => CType.capt (C.crename f) (S.crename f)

def SType.crename : SType n m k -> FinFun k k' -> SType n m k'
| SType.top, _ => SType.top
| SType.tvar X, _ => SType.tvar X
| SType.forall E1 E2, f => SType.forall (E1.crename f) (E2.crename f)
| SType.tforall S E, f => SType.tforall (S.crename f) (E.crename f)
| SType.cforall E, f => SType.cforall (E.crename f.ext)
| SType.box T, f => SType.box (T.crename f)

end

def EType.weaken (E : EType n m k) : EType (n+1) m k :=
  E.rename FinFun.weaken

def EType.weaken1 (E : EType (n+1) m k) : EType (n+2) m k :=
  E.rename FinFun.weaken.ext

def CType.weaken (C : CType n m k) : CType (n+1) m k :=
  C.rename FinFun.weaken

def SType.weaken (S : SType n m k) : SType (n+1) m k :=
  S.rename FinFun.weaken

def EType.tweaken (E : EType n m k) : EType n (m+1) k :=
  E.trename FinFun.weaken

def CType.tweaken (C : CType n m k) : CType n (m+1) k :=
  C.trename FinFun.weaken

def SType.tweaken (S : SType n m k) : SType n (m+1) k :=
  S.trename FinFun.weaken

def EType.cweaken (E : EType n m k) : EType n m (k+1) :=
  E.crename FinFun.weaken

def CType.cweaken (C : CType n m k) : CType n m (k+1) :=
  C.crename FinFun.weaken

def SType.cweaken (S : SType n m k) : SType n m (k+1) :=
  S.crename FinFun.weaken

def SType.cweaken1 (S : SType n m (k+1)) : SType n m (k+2) :=
  S.crename FinFun.weaken.ext

def CType.cweaken1 (T : CType n m (k+1)) : CType n m (k+2) :=
  T.crename FinFun.weaken.ext

def EType.cweaken1 (E : EType n m (k+1)) : EType n m (k+2) :=
  E.crename FinFun.weaken.ext

def EType.open (E : EType (n+1) m k) (x : Fin n) : EType n m k :=
  E.rename (FinFun.open x)

def CType.open (C : CType (n+1) m k) (x : Fin n) : CType n m k :=
  C.rename (FinFun.open x)

def SType.open (S : SType (n+1) m k) (x : Fin n) : SType n m k :=
  S.rename (FinFun.open x)

def EType.topen (E : EType n (m+1) k) (X : Fin m) : EType n m k :=
  E.trename (FinFun.open X)

def CType.topen (C : CType n (m+1) k) (X : Fin m) : CType n m k :=
  C.trename (FinFun.open X)

def SType.topen (S : SType n (m+1) k) (X : Fin m) : SType n m k :=
  S.trename (FinFun.open X)

def EType.copen (E : EType n m (k+1)) (x : Fin k) : EType n m k :=
  E.crename (FinFun.open x)

def CType.copen (C : CType n m (k+1)) (x : Fin k) : CType n m k :=
  C.crename (FinFun.open x)

def SType.copen (S : SType n m (k+1)) (x : Fin k) : SType n m k :=
  S.crename (FinFun.open x)


end Capless
