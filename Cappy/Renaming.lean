import Capless.Tactics
import Capless.Basic
namespace Cappy

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


end Cappy
