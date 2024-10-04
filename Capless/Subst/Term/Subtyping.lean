import Capless.Subst.Basic
import Capless.Subtyping
import Capless.Subst.Term.Subcapturing
namespace Capless

def SSubtyp.subst_motive1
  (Γ : Context n m k)
  (E1 : EType n m k)
  (E2 : EType n m k)
  : Prop :=
  ∀ {n'} (f : FinFun n n') (Δ : Context n' m k) (ρ : VarSubst Γ f Δ),
  ESubtyp Δ (E1.rename f) (E2.rename f)

def SSubtyp.subst_motive2
  (Γ : Context n m k)
  (C1 : CType n m k)
  (C2 : CType n m k)
  : Prop :=
  ∀ {n'} (f : FinFun n n') (Δ : Context n' m k) (ρ : VarSubst Γ f Δ),
  CSubtyp Δ (C1.rename f) (C2.rename f)

def SSubtyp.subst_motive3
  (Γ : Context n m k)
  (S1 : SType n m k)
  (S2 : SType n m k)
  : Prop :=
  ∀ {n'} (f : FinFun n n') (Δ : Context n' m k) (ρ : VarSubst Γ f Δ),
  SSubtyp Δ (S1.rename f) (S2.rename f)

theorem SSubtyp.subst
  (h : SSubtyp Γ S1 S2)
  (σ : VarSubst Γ f Δ) :
  SSubtyp Δ (S1.rename f) (S2.rename f) := by
  apply SSubtyp.rec
    (motive_1 := fun Γ E1 E2 h => SSubtyp.subst_motive1 Γ E1 E2)
    (motive_2 := fun Γ C1 C2 h => SSubtyp.subst_motive2 Γ C1 C2)
    (motive_3 := fun Γ S1 S2 h => SSubtyp.subst_motive3 Γ S1 S2)
    (t := h) (ρ := σ)
  case exist =>
    unfold subst_motive1 subst_motive2
    repeat intro
    simp [EType.rename]
    apply ESubtyp.exist
    rename_i ih _ _ _ _
    apply ih <;> try assumption
    apply VarSubst.cext; trivial
  case type =>
    unfold subst_motive1 subst_motive2
    repeat intro
    simp [EType.rename]
    apply ESubtyp.type
    aesop
  case capt =>
    unfold subst_motive2 subst_motive3
    repeat intro
    simp [CType.rename]
    apply CSubtyp.capt
    apply Subcapt.subst <;> trivial
    aesop
  case top =>
    unfold subst_motive3
    repeat intro
    simp [SType.rename]
    apply top
  case refl =>
    unfold subst_motive3
    repeat intro
    apply refl
  case trans =>
    unfold subst_motive3
    repeat intro
    apply trans
    { aesop }
    { aesop }
  case tvar =>
    unfold subst_motive3
    repeat intro
    simp [SType.rename]
    apply tvar
    rename_i hb _ _ _ σ
    have hb1 := σ.tmap _ _ hb
    simp [TBinding.rename] at hb1
    exact hb1
  case tinstl =>
    unfold subst_motive3
    repeat intro
    simp [SType.rename]
    apply tinstl
    rename_i hb _ _ _ σ
    have hb1 := σ.tmap _ _ hb
    simp [TBinding.rename] at hb1
    exact hb1
  case tinstr =>
    unfold subst_motive3
    repeat intro
    simp [SType.rename]
    apply tinstr
    rename_i hb _ _ _ σ
    have hb1 := σ.tmap _ _ hb
    simp [TBinding.rename] at hb1
    exact hb1
  case boxed =>
    unfold subst_motive2 subst_motive3
    repeat intro
    simp [SType.rename]
    apply boxed
    aesop
  case label =>
    unfold subst_motive3
    repeat intro
    apply label
    aesop
  case xforall =>
    unfold subst_motive1 subst_motive2 subst_motive3
    repeat intro
    simp [SType.rename]
    apply xforall
    { aesop }
    { rename_i ih _ _ _ σ
      apply ih <;> try assumption
      apply VarSubst.ext; trivial }
  case tforall =>
    unfold subst_motive1 subst_motive3
    repeat intro
    simp [SType.rename]
    apply tforall
    { aesop }
    { rename_i ih _ _ _ σ
      apply ih <;> try assumption
      apply VarSubst.text; trivial }
  case cforall =>
    unfold subst_motive1 subst_motive3
    repeat intro
    simp [SType.rename]
    apply cforall
    { rename_i ih _ _ _ σ
      apply ih <;> try assumption
      apply VarSubst.cext; trivial }

theorem CSubtyp.subst
  (h : CSubtyp Γ T1 T2)
  (σ : VarSubst Γ f Δ) :
  CSubtyp Δ (T1.rename f) (T2.rename f) := by
  cases h
  case capt hc hs =>
    simp [CType.rename]
    apply CSubtyp.capt
    { apply hc.subst; trivial }
    { apply hs.subst; trivial }

theorem ESubtyp.subst
  (h : ESubtyp Γ E1 E2)
  (σ : VarSubst Γ f Δ) :
  ESubtyp Δ (E1.rename f) (E2.rename f) := by
  cases h
  case exist hs =>
    simp [EType.rename]
    apply ESubtyp.exist
    { apply hs.subst
      apply σ.cext }
  case type hs =>
    simp [EType.rename]
    apply ESubtyp.type
    apply hs.subst; trivial

theorem ESubtyp.narrow
  (h : ESubtyp (Γ.var T) E1 E2)
  (hs : CSubtyp Γ T' T) :
  ESubtyp (Γ.var T') E1 E2 := by
  rw [<- EType.rename_id (E := E1), <- EType.rename_id (E := E2)]
  apply ESubtyp.subst
  { trivial }
  { apply VarSubst.narrow
    trivial }

end Capless
