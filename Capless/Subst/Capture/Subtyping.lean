import Capless.Subtyping
import Capless.Subst.Basic
import Capless.Subst.Capture.Subcapturing
namespace Capless

def SSubtyp.csubst_motive1
  (Γ : Context n m k)
  (E1 : EType n m k)
  (E2 : EType n m k)
  : Prop :=
  ∀ {k'} (f : FinFun k k') (Δ : Context n m k') (ρ : CVarSubst Γ f Δ),
  ESubtyp Δ (E1.crename f) (E2.crename f)

def SSubtyp.csubst_motive2
  (Γ : Context n m k)
  (C1 : CType n m k)
  (C2 : CType n m k)
  : Prop :=
  ∀ {k'} (f : FinFun k k') (Δ : Context n m k') (ρ : CVarSubst Γ f Δ),
  CSubtyp Δ (C1.crename f) (C2.crename f)

def SSubtyp.csubst_motive3
  (Γ : Context n m k)
  (S1 : SType n m k)
  (S2 : SType n m k)
  : Prop :=
  ∀ {k'} (f : FinFun k k') (Δ : Context n m k') (ρ : CVarSubst Γ f Δ),
  SSubtyp Δ (S1.crename f) (S2.crename f)

theorem SSubtyp.csubst
  (h : SSubtyp Γ S1 S2)
  (σ : CVarSubst Γ f Δ) :
  SSubtyp Δ (S1.crename f) (S2.crename f) := by
    apply SSubtyp.rec
      (motive_1 := fun Γ E1 E2 _ => SSubtyp.csubst_motive1 Γ E1 E2)
      (motive_2 := fun Γ C1 C2 _ => SSubtyp.csubst_motive2 Γ C1 C2)
      (motive_3 := fun Γ S1 S2 _ => SSubtyp.csubst_motive3 Γ S1 S2)
      (t := h) (ρ := σ)
    case exist =>
      unfold csubst_motive1 csubst_motive2
      repeat intro
      simp [EType.crename]
      apply ESubtyp.exist
      rename_i ih _ _ _ ρ
      apply ih ; try assumption
      apply CVarSubst.cext; trivial
    case type =>
      unfold csubst_motive1 csubst_motive2
      repeat intro
      simp [EType.crename]
      apply ESubtyp.type
      aesop
    case capt =>
      unfold csubst_motive2 csubst_motive3
      repeat intro
      simp [CType.crename]
      apply CSubtyp.capt
      apply Subcapt.csubst <;> trivial
      aesop
    case top =>
      unfold csubst_motive3
      repeat intro
      simp [SType.crename]
      apply top
    case refl =>
      unfold csubst_motive3
      repeat intro
      apply refl
    case trans =>
      unfold csubst_motive3
      repeat intro
      apply trans
      { aesop }
      { aesop }
    case tvar =>
      unfold csubst_motive3
      repeat intro
      rename_i hb _ _ _ σ
      have hb1 := σ.tmap _ _ hb
      simp [SType.crename]
      apply tvar
      trivial
    case tinstl =>
      unfold csubst_motive3
      repeat intro
      rename_i hb _ _ Δ σ
      have hb1 := σ.tmap _ _ hb
      simp [SType.crename]
      apply SSubtyp.tinstl
      trivial
    case tinstr =>
      unfold csubst_motive3
      repeat intro
      rename_i hb _ _ Δ σ
      have hb1 := σ.tmap _ _ hb
      simp [SType.crename]
      apply SSubtyp.tinstr
      trivial
    case boxed =>
      unfold csubst_motive2 csubst_motive3
      repeat intro
      simp [SType.crename]
      apply boxed
      aesop
    case xforall =>
      unfold csubst_motive1 csubst_motive2 csubst_motive3
      repeat intro
      simp [SType.crename]
      apply xforall
      { aesop }
      { rename_i ih _ _ _ σ
        apply ih ; try assumption
        apply CVarSubst.ext; trivial }
    case tforall =>
      unfold csubst_motive1 csubst_motive3
      repeat intro
      simp [SType.crename]
      apply tforall
      { aesop }
      { rename_i ih _ _ _ σ
        apply ih ; try assumption
        rw [<-TBinding.crename_bound]
        apply CVarSubst.text; trivial }
    case cforall =>
      unfold csubst_motive1 csubst_motive3
      repeat intro
      simp [SType.crename]
      apply cforall
      { rename_i ih _ _ _ σ
        apply ih ; try assumption
        apply CVarSubst.cext; trivial
      }

theorem CSubtyp.csubst
  (h : CSubtyp Γ T1 T2)
  (σ : CVarSubst Γ f Δ) :
  CSubtyp Δ (T1.crename f) (T2.crename f) := by
  cases h
  case capt hc hs =>
    simp [CType.crename]
    apply CSubtyp.capt
    { apply hc.csubst; trivial }
    { apply hs.csubst; trivial }

theorem ESubtyp.csubst
  (h : ESubtyp Γ E1 E2)
  (σ : CVarSubst Γ f Δ) :
  ESubtyp Δ (E1.crename f) (E2.crename f) := by
  cases h
  case exist hs =>
    simp [EType.crename]
    apply ESubtyp.exist
    { apply hs.csubst
      apply σ.cext }
  case type hs =>
    simp [EType.crename]
    apply ESubtyp.type
    apply hs.csubst; trivial


end Capless
