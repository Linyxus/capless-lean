import Cappy.Syntax.CaptureSet
import Cappy.Renaming

namespace Cappy

inductive Annot : Type where
| eps : Annot
| use : Annot

mutual

inductive CType : Nat -> Nat -> Type where
| capt : CaptureSet n -> SType n m -> CType n m

inductive SType : Nat -> Nat -> Type where
| top : SType n m
| tvar : Fin m -> SType n m
| arrow : Annot -> CType n m -> CType (n+1) m -> SType n m
| tarrow : SType n m -> CType n (m+1) -> SType n m
| boxed : CType n m -> SType n m

end

notation:max S "^" C => CType.capt C S
notation:50 "∀(x:" T ")" U => SType.arrow Annot.eps T U
notation:50 "∀(use x:" T ")" U => SType.arrow Annot.use T U
notation:50 "∀[X<:" S "]" T => SType.tarrow S T

mutual

def CType.rename : CType n m -> RenameFun n m n' m' -> CType n' m'
| CType.capt C S, f => (S.rename f)^(C.rename f.map)

def SType.rename : SType n m -> RenameFun n m n' m' -> SType n' m'
| SType.top, _ => SType.top
| SType.tvar x, f => SType.tvar (f.tmap x)
| SType.arrow a T U, f => SType.arrow a (T.rename f) (U.rename f.ext)
| SType.tarrow S T, f => SType.tarrow (S.rename f) (T.rename f.text)
| SType.boxed C, f => SType.boxed (C.rename f)

end

def CType.weaken (T : CType n m) : CType (n+1) m :=
  T.rename RenameFun.weaken

def SType.weaken (T : SType n m) : SType (n+1) m :=
  T.rename RenameFun.weaken

def CType.tweaken (T : CType n m) : CType n (m+1) :=
  T.rename RenameFun.tweaken

def SType.tweaken (T : SType n m) : SType n (m+1) :=
  T.rename RenameFun.tweaken

end Cappy
