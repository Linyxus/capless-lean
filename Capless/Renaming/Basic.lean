import Capless.Basic
import Capless.Context
import Capless.CaptureSet
namespace Capless

-- def VarRename (Γ : Context n m k) (f : FinFun n n') (Δ : Context n' m k) : Prop :=
--   ∀ x E, Γ.Bound x E -> Δ.Bound (f x) (E.rename f)

structure VarMap (Γ : Context n m k) (f : FinFun n n') (Δ : Context n' m k) where
  map : ∀ x E, Γ.Bound x E -> Δ.Bound (f x) (E.rename f)
  tmap : ∀ X b, Γ.TBound X b -> Δ.TBound X (b.rename f)
  cmap : ∀ c b, Γ.CBound c b -> Δ.CBound c (b.rename f)

def VarMap.cext {Γ : Context n m k} {Δ : Context n' m k}
  (ρ : VarMap Γ f Δ) (b : CBinding n k) :
  VarMap (Γ.cvar b) f (Δ.cvar (b.rename f)) := by
  constructor
  · intros x E hb
    cases hb
    simp [CType.cweaken_rename_comm]
    constructor
    apply ρ.map; assumption
  · intros X B hb
    cases hb
    simp [TBinding.cweaken_rename_comm]
    constructor
    apply ρ.tmap; assumption
  · intros c B hb
    cases hb
    case here =>
      simp [CBinding.cweaken_rename_comm]
      constructor
    case there_cvar =>
      simp [CBinding.cweaken_rename_comm]
      constructor
      apply ρ.cmap; assumption

def VarMap.ext {Γ : Context n m k} {Δ : Context n' m k}
  (ρ : VarMap Γ f Δ) (E : CType n m k) :
  VarMap (Γ.var E) f.ext (Δ.var (E.rename f)) := by
  constructor
  · intros x E' hb
    cases hb
    case here =>
      rw [<- CType.weaken_rename]
      constructor
    case there_var =>
      rw [<- CType.weaken_rename]
      simp [FinFun.ext]
      constructor
      apply ρ.map; trivial
  · intros X B hb
    cases hb
    case there_var =>
      rw [<- TBinding.weaken_rename]
      constructor
      apply ρ.tmap; assumption
  · intros c B hb
    cases hb
    case there_var =>
      rw [<- CBinding.weaken_rename]
      constructor
      apply ρ.cmap; assumption

def VarMap.text {Γ : Context n m k} {Δ : Context n' m k}
  (ρ : VarMap Γ f Δ) (b : TBinding n m k) :
  VarMap (Γ.tvar b) f (Δ.tvar (b.rename f)) := by
  constructor
  case map =>
    intros x E hb
    cases hb
    case there_tvar =>
      rw [CType.tweaken_rename]
      constructor
      apply ρ.map; assumption
  case tmap =>
    intros X b hb
    cases hb
    case here =>
      rw [TBinding.tweaken_rename_comm]
      constructor
    case there_tvar =>
      rw [TBinding.tweaken_rename_comm]
      constructor
      apply ρ.tmap; assumption
  case cmap =>
    intros c b hb
    cases hb
    case there_tvar =>
      constructor
      apply ρ.cmap; assumption

structure CVarMap (Γ : Context n m k) (f : FinFun k k') (Δ : Context n m k') where
  map : ∀ x E, Γ.Bound x E -> Δ.Bound x (E.crename f)
  tmap : ∀ X b, Γ.TBound X b -> Δ.TBound X (b.crename f)
  cmap : ∀ c b, Γ.CBound c b -> Δ.CBound (f c) (b.crename f)

def CVarMap.cext {Γ : Context n m k} {Δ : Context n m k'}
  (ρ : CVarMap Γ f Δ) (b : CBinding n k) :
  CVarMap (Γ.cvar b) f.ext (Δ.cvar (b.crename f)) := by
  constructor
  case map =>
    intro x E hb
    cases hb
    case there_cvar hb0 =>
      rw [<- CType.cweaken_crename]
      constructor
      apply ρ.map; assumption
  case tmap =>
    intro x S hb
    cases hb
    case there_cvar hb0 =>
      rw [<- TBinding.cweaken_crename]
      constructor
      apply ρ.tmap; assumption
  case cmap =>
    intro c b hb
    cases hb
    case here =>
      rw [<- CBinding.cweaken_crename]
      constructor
    case there_cvar hb0 =>
      rw [<- CBinding.cweaken_crename]
      constructor
      apply ρ.cmap; assumption

def CVarMap.ext {Γ : Context n m k} {Δ : Context n m k'}
  (ρ : CVarMap Γ f Δ) (E : CType n m k) :
  CVarMap (Γ.var E) f (Δ.var (E.crename f)) := by
  constructor
  case map =>
    intro x E hb
    cases hb
    case here =>
      rw [<- CType.weaken_crename]
      constructor
    case there_var hb0 =>
      rw [<- CType.weaken_crename]
      constructor
      apply ρ.map; assumption
  case tmap =>
    intro x b hb
    cases hb
    case there_var =>
      rw [<- TBinding.weaken_crename]
      constructor
      apply ρ.tmap; assumption
  case cmap =>
    intro c b hb
    cases hb
    case there_var =>
      rw [<- CBinding.weaken_crename]
      constructor
      apply ρ.cmap; assumption

def CVarMap.text {Γ : Context n m k} {Δ : Context n m k'}
  (ρ : CVarMap Γ f Δ) (b : TBinding n m k) :
  CVarMap (Γ.tvar b) f (Δ.tvar (b.crename f)) := by
  constructor
  case map =>
    intro x E hb
    cases hb
    case there_tvar hb0 =>
      rw [<- CType.tweaken_crename]
      constructor
      apply ρ.map; assumption
  case tmap =>
    intro x b hb
    cases hb
    case here =>
      rw [<- TBinding.tweaken_crename]
      constructor
    case there_tvar hb0 =>
      rw [<- TBinding.tweaken_crename]
      constructor
      apply ρ.tmap; assumption
  case cmap =>
    intro c b hb
    cases hb
    case there_tvar hb0 =>
      constructor
      apply ρ.cmap; assumption

structure TVarMap (Γ : Context n m k) (f : FinFun m m') (Δ : Context n m' k) where
  map : ∀ x E, Γ.Bound x E -> Δ.Bound x (E.trename f)
  tmap : ∀ X b, Γ.TBound X b -> Δ.TBound (f X) (b.trename f)
  cmap : ∀ c b, Γ.CBound c b -> Δ.CBound c b

def TVarMap.ext {Γ : Context n m k} {Δ : Context n m' k}
  (ρ : TVarMap Γ f Δ) (E : CType n m k) :
  TVarMap (Γ.var E) f (Δ.var (E.trename f)) := by
  constructor
  case map =>
    intro x E hb
    cases hb
    case here =>
      rw [<- CType.weaken_trename]
      constructor
    case there_var hb0 =>
      rw [<- CType.weaken_trename]
      constructor
      apply ρ.map; assumption
  case tmap =>
    intro x b hb
    cases hb
    case there_var =>
      rw [<- TBinding.weaken_trename]
      constructor
      apply ρ.tmap; assumption
  case cmap =>
    intro c b hb
    cases hb
    case there_var =>
      constructor
      apply ρ.cmap; assumption

def TVarMap.text {Γ : Context n m k} {Δ : Context n m' k}
  (ρ : TVarMap Γ f Δ) (b : TBinding n m k) :
  TVarMap (Γ.tvar b) f.ext (Δ.tvar (b.trename f)) := by
  constructor
  case map =>
    intro x E hb
    cases hb
    case there_tvar hb0 =>
      rw [<- CType.tweaken_trename]
      constructor
      apply ρ.map; assumption
  case tmap =>
    intro x b hb
    cases hb
    case here =>
      rw [<- TBinding.tweaken_trename]
      constructor
    case there_tvar hb0 =>
      rw [<- TBinding.tweaken_trename]
      constructor
      apply ρ.tmap; assumption
  case cmap =>
    intro c b hb
    cases hb
    case there_tvar hb0 =>
      constructor
      apply ρ.cmap; assumption

def TVarMap.cext {Γ : Context n m k} {Δ : Context n m' k}
  (ρ : TVarMap Γ f Δ) (b : CBinding n k) :
  TVarMap (Γ.cvar b) f (Δ.cvar b) := by
  constructor
  case map =>
    intro x E hb
    cases hb
    case there_cvar hb0 =>
      rw [<- CType.cweaken_trename]
      constructor
      apply ρ.map; assumption
  case tmap =>
    intro x b hb
    cases hb
    case there_cvar hb0 =>
      rw [<- TBinding.cweaken_trename]
      constructor
      apply ρ.tmap; assumption
  case cmap =>
    intro c b hb
    cases hb
    case here =>
      constructor
    case there_cvar hb0 =>
      constructor
      apply ρ.cmap; assumption
