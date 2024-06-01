import Capless.Type
import Capless.CaptureSet
namespace Capless

inductive TBinding : Nat -> Nat -> Nat -> Type where
| bound : SType n m k -> TBinding n m k
| inst : SType n m k -> TBinding n m k

inductive CBinding : Nat -> Nat -> Type where
| bound : CBinding n k
| inst : CaptureSet n k -> CBinding n k

def TBinding.weaken : TBinding n m k -> TBinding (n+1) m k
| bound S => bound S.weaken
| inst S => inst S.weaken

def CBinding.weaken : CBinding n k -> CBinding (n+1) k
| bound => bound
| inst C => inst C.weaken

def TBinding.tweaken : TBinding n m k -> TBinding n (m+1) k
| bound S => bound S.tweaken
| inst S => inst S.tweaken

def TBinding.cweaken : TBinding n m k -> TBinding n m (k+1)
| bound S => bound S.cweaken
| inst S => inst S.cweaken

def CBinding.cweaken : CBinding n k -> CBinding n (k+1)
| bound => bound
| inst C => inst C.cweaken

inductive Context : Nat -> Nat -> Nat -> Type where
| empty : Context 0 0 0
| var : Context n m k -> EType n m k -> Context (n+1) m k
| tvar : Context n m k -> TBinding n m k -> Context n (m+1) k
| cvar : Context n m k -> CBinding n k -> Context n m (k+1)

inductive Context.Bound : Context n m k -> Fin n -> EType n m k -> Prop where
| here : Bound (var Γ0 E) 0 E.weaken
| there_var :
  Bound Γ x E ->
  Bound (var Γ E') (Fin.succ x) E.weaken
| there_tvar :
  Bound Γ x E ->
  Bound (tvar Γ b) x E.tweaken
| there_cvar :
  Bound Γ x E ->
  Bound (cvar Γ b) x E.cweaken

inductive Context.TBound : Context n m k -> Fin m -> TBinding n m k -> Prop where
| here : TBound (tvar Γ0 b) 0 b.tweaken
| there_var :
  TBound Γ x b ->
  TBound (var Γ E) x b.weaken
| there_tvar :
  TBound Γ x b ->
  TBound (tvar Γ b') (Fin.succ x) b.tweaken
| there_cvar :
  TBound Γ x b ->
  TBound (cvar Γ b') x b.cweaken

inductive Context.CBound : Context n m k -> Fin k -> CBinding n k -> Prop where
| here : CBound (cvar Γ0 b) 0 b.cweaken
| there_var :
  CBound Γ x b ->
  CBound (var Γ E) x b.weaken
| there_tvar :
  CBound Γ x b ->
  CBound (tvar Γ b') x b
| there_cvar :
  CBound Γ x b ->
  CBound (cvar Γ b') (Fin.succ x) b.cweaken

end Capless
