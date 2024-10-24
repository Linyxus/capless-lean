import Capless.Tactics
import Capless.Basic
import Mathlib.Data.Fin.Basic
import Cappy.CaptureSet
namespace Cappy

inductive Annot : Type where
| eps : Annot
| use : Annot

structure RenameFun (n m n' m' : Nat) where
  map : Capless.FinFun n n'
  tmap : Capless.FinFun m m'

def RenameFun.ext (f : RenameFun n m n' m') : RenameFun (n+1) m (n'+1) m' :=
  { map := f.map.ext, tmap := f.tmap }

def RenameFun.text (f : RenameFun n m n' m') : RenameFun n (m+1) n' (m'+1) :=
  { map := f.map, tmap := f.tmap.ext }

def RenameFun.weaken : RenameFun n m (n+1) m :=
  { map := Capless.FinFun.weaken, tmap := Capless.FinFun.id }

def RenameFun.tweaken : RenameFun n m n (m+1) :=
  { map := Capless.FinFun.id, tmap := Capless.FinFun.weaken }

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

inductive Term : Nat -> Nat -> Type where
| var : Fin n -> Term n m
| abs : Annot -> CType n m -> Term (n+1) m -> Term n m
| app : Fin n -> Fin n -> Term n m
| tabs : SType n m -> Term n (m+1) -> Term n m
| tapp : Fin m -> SType n m -> Term n m
| box : Fin n -> Term n m
| unbox : CaptureSet n -> Fin n -> Term n m
| letin : Term n m -> Term (n+1) m -> Term n m

inductive Context : Nat -> Nat -> Type where
| empty : Context 0 0
| var : Context n m -> CType n m -> Context (n+1) m
| tvar : Context n m -> SType n m -> Context n (m+1)

inductive Context.Bound : Context n m -> Fin n -> CType n m -> Prop where
| here :
  Context.Bound (Context.var Γ T) 0 T.weaken
| there_var :
  Context.Bound Γ x T ->
  Context.Bound (Context.var Γ T') x.succ T.weaken
| there_tvar :
  Context.Bound Γ x T ->
  Context.Bound (Context.tvar Γ S) x T.tweaken

inductive Context.TBound : Context n m -> Fin m -> SType n m -> Prop where
| here :
  Context.TBound (Context.tvar Γ S) 0 S.tweaken
| there_var :
  Context.TBound Γ x S ->
  Context.TBound (Context.var Γ T) x S.weaken
| there_tvar :
  Context.TBound Γ x S ->
  Context.TBound (Context.tvar Γ S') x.succ S.tweaken

inductive Subcapt : Context n m -> CaptureSet n -> CaptureSet n -> Prop where
| sc_trans :
  Subcapt Γ C1 C2 ->
  Subcapt Γ C2 C3 ->
  Subcapt Γ C1 C3
| sc_var :
  Context.Bound Γ x (S^C) ->
  Subcapt Γ {x=x} C
| sc_elem {C1 C2 : CaptureSet n} :
  C1 ⊆ C2 ->
  Subcapt Γ C1 C2
| sc_set :
  Subcapt Γ C1 C ->
  Subcapt Γ C2 C ->
  Subcapt Γ (C1 ∪ C2) C

mutual

inductive CSubtyp : Context n m -> CType n m -> CType n m -> Prop where
| capt :
  Subcapt Γ C1 C2 ->
  SSubtyp Γ S1 S2 ->
  CSubtyp Γ (S1^C1) (S2^C2)

inductive SSubtyp : Context n m -> SType n m -> SType n m -> Prop where
| top :
  SSubtyp Γ S SType.top
| refl :
  SSubtyp Γ S S
| trans :
  SSubtyp Γ S1 S2 ->
  SSubtyp Γ S2 S3 ->
  SSubtyp Γ S1 S3
| tvar :
  Context.TBound Γ X S ->
  SSubtyp Γ (SType.tvar X) S
| boxed :
  CSubtyp Γ T1 T2 ->
  SSubtyp Γ (SType.boxed T1) (SType.boxed T2)
| arrow :
  CSubtyp Γ T2 T1 ->
  CSubtyp (Γ.var T2) U1 U2 ->
  SSubtyp Γ (∀(x:T1)U1) (SType.arrow a T2 U2)
| uarrow :
  CSubtyp (Γ.var T) U1 U2 ->
  SSubtyp Γ (∀(use x:T)U1) (∀(use x:T)U2)
| tarrow :
  SSubtyp Γ S2 S1 ->
  CSubtyp (Γ.tvar S2) T1 T2 ->
  SSubtyp Γ (∀[X<:S1]T1) (∀[X<:S2]T2)

end

mutual

inductive CType.CapRefine : CaptureSet n -> CType n m -> CType n m -> Prop where
| r_capt :
  SType.CapRefine D S S' ->
  CType.CapRefine D (S^C) (S'^(C.open_cap D))

inductive SType.CapRefine : CaptureSet n -> SType n m -> SType n m -> Prop where
| r_top :
  SType.CapRefine D top top
| r_tvar :
  SType.CapRefine D (SType.tvar X) (SType.tvar X)
| r_fun :
  CType.CapRefine (D.weaken ∪ {x=0} ∪ {x*=0}) U U' ->
  SType.CapRefine D (SType.arrow a T U) (SType.arrow a T U')
| r_tfun :
  CType.CapRefine D T T' ->
  SType.CapRefine D (SType.tarrow S T) (SType.tarrow S T')
| r_boxed :
  CType.CapRefine D T T' ->
  SType.CapRefine D (SType.boxed T) (SType.boxed T')

end

end Cappy
