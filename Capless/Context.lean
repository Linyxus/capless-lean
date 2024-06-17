import Capless.Type
import Capless.CaptureSet
namespace Capless

inductive TBinding : Nat -> Nat -> Nat -> Type where
| bound : SType n m k -> TBinding n m k
| inst : SType n m k -> TBinding n m k

inductive CBinding : Nat -> Nat -> Type where
| bound : CBinding n k
| inst : CaptureSet n k -> CBinding n k

def TBinding.rename (b : TBinding n m k) (f : FinFun n n') : TBinding n' m k :=
  match b with
  | bound S => bound (S.rename f)
  | inst S => inst (S.rename f)

def TBinding.trename (b : TBinding n m k) (f : FinFun m m') : TBinding n m' k :=
  match b with
  | bound S => bound (S.trename f)
  | inst S => inst (S.trename f)

def TBinding.crename (b : TBinding n m k) (f : FinFun k k') : TBinding n m k' :=
  match b with
  | bound S => bound (S.crename f)
  | inst S => inst (S.crename f)

def CBinding.rename (b : CBinding n k) (f : FinFun n n') : CBinding n' k :=
  match b with
  | bound => bound
  | inst C => inst (C.rename f)

def CBinding.crename (b : CBinding n k) (f : FinFun k k') : CBinding n k' :=
  match b with
  | bound => bound
  | inst C => inst (C.crename f)

def TBinding.weaken (b : TBinding n m k) : TBinding (n+1) m k :=
  b.rename FinFun.weaken

def CBinding.weaken (b : CBinding n k) : CBinding (n+1) k :=
  b.rename FinFun.weaken

def TBinding.tweaken (b : TBinding n m k) : TBinding n (m+1) k :=
  b.trename FinFun.weaken

def TBinding.cweaken (b : TBinding n m k) : TBinding n m (k+1) :=
  b.crename FinFun.weaken

def CBinding.cweaken (b : CBinding n k) : CBinding n (k+1) :=
  b.crename FinFun.weaken

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

theorem CBinding.crename_rename_comm {b : CBinding n k} :
  (b.crename f).rename g = (b.rename g).crename f := by
  cases b
  case bound => simp [rename, crename]
  case inst => simp [rename, crename, CaptureSet.crename_rename_comm]

theorem TBinding.crename_rename_comm {b : TBinding n m k} :
  (b.crename f).rename g = (b.rename g).crename f := by
  cases b
  case bound => simp [rename, crename, SType.crename_rename_comm]
  case inst => simp [rename, crename, SType.crename_rename_comm]

theorem CBinding.cweaken_rename_comm {b : CBinding n k} :
  b.cweaken.rename f = (b.rename f).cweaken := by
  simp [cweaken, crename_rename_comm]

theorem TBinding.cweaken_rename_comm {b : TBinding n m k} :
  b.cweaken.rename f = (b.rename f).cweaken := by
  simp [cweaken, crename_rename_comm]

theorem TBinding.rename_rename {b : TBinding n m k} :
  (b.rename f).rename g = b.rename (g ∘ f) := by
  cases b
  case bound => simp [rename, SType.rename_rename]
  case inst => simp [rename, SType.rename_rename]

theorem CBinding.rename_rename {b : CBinding n k} :
  (b.rename f).rename g = b.rename (g ∘ f) := by
  cases b
  case bound => simp [rename]
  case inst => simp [rename, CaptureSet.rename_rename]

theorem TBinding.crename_crename {b : TBinding n m k} :
  (b.crename f).crename g = b.crename (g ∘ f) := by
  cases b
  case bound => simp [crename, SType.crename_crename]
  case inst => simp [crename, SType.crename_crename]

theorem CBinding.crename_crename {b : CBinding n k} :
  (b.crename f).crename g = b.crename (g ∘ f) := by
  cases b
  case bound => simp [crename]
  case inst => simp [crename, CaptureSet.crename_crename]

theorem TBinding.trename_trename {b : TBinding n m k} :
  (b.trename f).trename g = b.trename (g ∘ f) := by
  cases b
  case bound => simp [trename, SType.trename_trename]
  case inst => simp [trename, SType.trename_trename]

theorem TBinding.cweaken_crename {b : TBinding n m k} :
  (b.crename f).cweaken = b.cweaken.crename f.ext := by
  simp [cweaken, crename_crename, FinFun.comp_weaken]

theorem CBinding.cweaken_crename {b : CBinding n k} :
  (b.crename f).cweaken = b.cweaken.crename f.ext := by
  simp [cweaken, crename_crename, FinFun.comp_weaken]

theorem TBinding.weaken_rename {b : TBinding n m k} :
  (b.rename f).weaken = b.weaken.rename f.ext := by
  simp [weaken, rename_rename, FinFun.comp_weaken]

theorem CBinding.weaken_rename {b : CBinding n k} :
  (b.rename f).weaken = b.weaken.rename f.ext := by
  simp [weaken, rename_rename, FinFun.comp_weaken]

theorem TBinding.trename_rename_comm {b : TBinding n m k} :
  (b.rename f).trename g = (b.trename g).rename f := by
  cases b
  case bound => simp [rename, trename, SType.trename_rename_comm]
  case inst => simp [rename, trename, SType.trename_rename_comm]

theorem TBinding.tweaken_rename_comm {b : TBinding n m k} :
  b.tweaken.rename f = (b.rename f).tweaken := by
  simp [tweaken, trename_rename_comm]

theorem TBinding.weaken_crename {b : TBinding n m k} :
  (b.crename f).weaken = b.weaken.crename f := by
  simp [weaken, crename_rename_comm]

theorem CBinding.weaken_crename {b : CBinding n k} :
  (b.crename f).weaken = b.weaken.crename f := by
  simp [weaken, crename_rename_comm]

theorem TBinding.crename_trename_comm {b : TBinding n m k} :
  (b.trename f).crename g = (b.crename g).trename f := by
  cases b
  case bound => simp [trename, crename, SType.crename_trename_comm]
  case inst => simp [trename, crename, SType.crename_trename_comm]

theorem TBinding.tweaken_crename {b : TBinding n m k} :
  (b.crename f).tweaken = b.tweaken.crename f := by
  simp [tweaken, crename_trename_comm]

theorem TBinding.tweaken_trename {b : TBinding n m k} :
  (b.trename f).tweaken = b.tweaken.trename f.ext := by
  simp [tweaken, trename_trename, FinFun.comp_weaken]

theorem TBinding.weaken_trename {b : TBinding n m k} :
  (b.trename f).weaken = b.weaken.trename f := by
  simp [weaken, trename_rename_comm]

theorem TBinding.cweaken_trename {b : TBinding n m k} :
  (b.trename f).cweaken = b.cweaken.trename f := by
  simp [cweaken, crename_trename_comm]

end Capless
