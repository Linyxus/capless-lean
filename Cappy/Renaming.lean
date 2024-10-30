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

def RenameFun.comp (g : RenameFun n' m' n'' m'') (f : RenameFun n m n' m') : RenameFun n m n'' m'' :=
  { map := g.map ∘ f.map, tmap := g.tmap ∘ f.tmap }

theorem RenameFun.comp_ext {g : RenameFun n' m' n'' m''} {f : RenameFun n m n' m'} :
  (g.comp f).ext = g.ext.comp f.ext := by
  simp [RenameFun.comp, RenameFun.ext]
  simp [Capless.FinFun.ext_comp_ext]

theorem RenameFun.comp_text {g : RenameFun n' m' n'' m''} {f : RenameFun n m n' m'} :
  (g.comp f).text = g.text.comp f.text := by
  simp [RenameFun.comp, RenameFun.text]
  simp [Capless.FinFun.ext_comp_ext]

end Cappy
