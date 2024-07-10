import Capless.Subst.Basic
import Capless.Subtyping
import Capless.Subst.Term.Subcapturing
namespace Capless

def SSubtyp.rename_motive1
  (Γ : Context n m k)
  (E1 : EType n m k)
  (E2 : EType n m k)
  : Prop :=
  ∀ {n'} (f : FinFun n n') (Δ : Context n' m k) (ρ : VarSubst Γ f Δ),
  ESubtyp Δ (E1.rename f) (E2.rename f)

def SSubtyp.rename_motive2
  (Γ : Context n m k)
  (C1 : CType n m k)
  (C2 : CType n m k)
  : Prop :=
  ∀ {n'} (f : FinFun n n') (Δ : Context n' m k) (ρ : VarSubst Γ f Δ),
  CSubtyp Δ (C1.rename f) (C2.rename f)

def SSubtyp.rename_motive3
  (Γ : Context n m k)
  (S1 : SType n m k)
  (S2 : SType n m k)
  : Prop :=
  ∀ {n'} (f : FinFun n n') (Δ : Context n' m k) (ρ : VarSubst Γ f Δ),
  SSubtyp Δ (S1.rename f) (S2.rename f)

theorem SSubtyp.rename
  (h : SSubtyp Γ S1 S2)
  (σ : VarSubst Γ f Δ) :
  SSubtyp Δ (S1.rename f) (S2.rename f) := by
  apply SSubtyp.rec
    (motive_1 := fun Γ E1 E2 h => SSubtyp.rename_motive1 Γ E1 E2)
    (motive_2 := fun Γ C1 C2 h => SSubtyp.rename_motive2 Γ C1 C2)
    (motive_3 := fun Γ S1 S2 h => SSubtyp.rename_motive3 Γ S1 S2)
    (t := h) (ρ := σ)
  case exist =>
    unfold rename_motive1 rename_motive2
    repeat intro
    simp [EType.rename]
    apply ESubtyp.exist
    rename_i ih _ _ _ _
    apply ih <;> try assumption
    sorry
  case type => sorry
  case capt => sorry
  case top => sorry
  case refl => sorry
  case trans => sorry
  case tvar => sorry
  case tinstl => sorry
  case tinstr => sorry
  case boxed => sorry
  case xforall => sorry
  case tforall => sorry
  case cforall => sorry

end Capless
