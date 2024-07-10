import Capless.Basic
import Capless.Context
import Capless.CaptureSet
import Capless.Typing
import Capless.Renaming.Term.Typing
import Capless.Renaming.Type.Typing
import Capless.Renaming.Capture.Typing
namespace Capless

structure VarSubst (Γ : Context n m k) (f : FinFun n n') (Δ : Context n' m k) where
  map : ∀ x E, Γ.Bound x E -> Typed Δ (Term.var (f x)) (EType.type (E.rename f))
  tmap : ∀ X b, Γ.TBound X b -> Δ.TBound X (b.rename f)
  cmap : ∀ c b, Γ.CBound c b -> Δ.CBound c (b.rename f)

def VarSubst.ext {Γ : Context n m k}
  (σ : VarSubst Γ f Δ)
  (T : CType n m k) :
  VarSubst (Γ.var T) f.ext (Δ.var (T.rename f)) := by
  constructor
  case map =>
    intros x E hb
    cases hb
    case here =>
      simp [FinFun.ext]
      apply Typed.var
      rw [<- CType.weaken_rename]
      constructor
    case there_var hb0 =>
      simp [FinFun.ext]
      rw [<- CType.weaken_rename]
      have h0 := σ.map _ _ hb0
      have h1 := Typed.weaken h0 (T := T.rename f)
      simp [Term.weaken, Term.rename, FinFun.weaken] at h1
      simp [EType.weaken, EType.rename, CType.weaken] at *
      exact h1
  case tmap =>
    intros X b hb
    cases hb
    case there_var hb0 =>
      have hb1 := σ.tmap _ _ hb0
      rw [<- TBinding.weaken_rename]
      constructor; trivial
  case cmap =>
    intros x b hb
    cases hb
    case there_var hb0 =>
      have hb1 := σ.cmap _ _ hb0
      rw [<- CBinding.weaken_rename]
      constructor; trivial

def VarSubst.text {Γ : Context n m k}
  (σ : VarSubst Γ f Δ) :
  VarSubst (Γ.tvar b) f (Δ.tvar (b.rename f)) := by
  constructor
  case map =>
    intros x T hb
    cases hb
    case there_tvar hb0 =>
      have h0 := σ.map _ _ hb0
      have h1 := h0.tweaken (b := (b.rename f))
      rw [CType.tweaken_rename]
      simp [EType.tweaken, EType.trename,
            CType.tweaken, Term.tweaken, Term.trename] at *
      exact h1
  case tmap =>
    intros X b hb
    cases hb
    case here =>
      rw [TBinding.tweaken_rename_comm]
      constructor
    case there_tvar hb0 =>
      have hb1 := σ.tmap _ _ hb0
      rw [TBinding.tweaken_rename_comm]
      constructor; trivial
  case cmap =>
    intros c b hb
    cases hb
    case there_tvar hb0 =>
      have hb1 := σ.cmap _ _ hb0
      constructor; trivial

def VarSubst.cext {Γ : Context n m k}
  (σ : VarSubst Γ f Δ) :
  VarSubst (Γ.cvar b) f (Δ.cvar (b.rename f)) := by
  constructor
  case map =>
    intros x T hb
    cases hb
    case there_cvar hb0 =>
      have h0 := σ.map _ _ hb0
      have h1 := h0.cweaken (b := (b.rename f))
      rw [CType.cweaken_rename_comm]
      simp [EType.cweaken, EType.crename,
            CType.cweaken, Term.cweaken, Term.crename] at *
      exact h1
  case tmap =>
    intros X b hb
    cases hb
    case there_cvar hb0 =>
      have hb1 := σ.tmap _ _ hb0
      rw [TBinding.cweaken_rename_comm]
      constructor; trivial
  case cmap =>
    intros c b hb
    cases hb
    case here =>
      rw [CBinding.cweaken_rename_comm]
      constructor
    case there_cvar hb0 =>
      have hb1 := σ.cmap _ _ hb0
      rw [CBinding.cweaken_rename_comm]
      constructor; trivial

end Capless
