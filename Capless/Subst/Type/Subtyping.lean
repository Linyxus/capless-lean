import Capless.Subst.Basic
import Capless.Subtyping
import Capless.Subst.Type.Subcapturing
namespace Capless

def SSubtyp.tsubst_motive1
  (Γ : Context n m k)
  (E1 : EType n m k)
  (E2 : EType n m k)
  : Prop :=
  ∀ {m'} (f : FinFun m m') (Δ : Context n m' k) (ρ : TVarSubst Γ f Δ),
  ESubtyp Δ (E1.trename f) (E2.trename f)

def SSubtyp.tsubst_motive2
  (Γ : Context n m k)
  (C1 : CType n m k)
  (C2 : CType n m k)
  : Prop :=
  ∀ {m'} (f : FinFun m m') (Δ : Context n m' k) (ρ : TVarSubst Γ f Δ),
  CSubtyp Δ (C1.trename f) (C2.trename f)

def SSubtyp.tsubst_motive3
  (Γ : Context n m k)
  (S1 : SType n m k)
  (S2 : SType n m k)
  : Prop :=
  ∀ {m'} (f : FinFun m m') (Δ : Context n m' k) (ρ : TVarSubst Γ f Δ),
  SSubtyp Δ (S1.trename f) (S2.trename f)

theorem SSubtyp.tsubst
  (h : SSubtyp Γ S1 S2)
  (σ : TVarSubst Γ f Δ) :
  SSubtyp Δ (S1.trename f) (S2.trename f) := by
    apply SSubtyp.rec
      (motive_1 := fun Γ E1 E2 _ => SSubtyp.tsubst_motive1 Γ E1 E2)
      (motive_2 := fun Γ C1 C2 _ => SSubtyp.tsubst_motive2 Γ C1 C2)
      (motive_3 := fun Γ S1 S2 _ => SSubtyp.tsubst_motive3 Γ S1 S2)
      (t := h) (ρ := σ)
    case exist =>
      unfold tsubst_motive1 tsubst_motive2
      repeat intro
      simp [EType.trename]
      apply ESubtyp.exist
      rename_i ih _ _ _ ρ
      apply ih ; try assumption
      apply TVarSubst.cext; trivial
    case type =>
      unfold tsubst_motive1 tsubst_motive2
      repeat intro
      simp [EType.trename]
      apply ESubtyp.type
      aesop
    case capt =>
      unfold tsubst_motive2 tsubst_motive3
      repeat intro
      simp [CType.trename]
      apply CSubtyp.capt
      apply Subcapt.tsubst <;> trivial
      aesop
    case top =>
      unfold tsubst_motive3
      repeat intro
      simp [SType.trename]
      apply top
    case refl =>
      unfold tsubst_motive3
      repeat intro
      apply refl
    case trans =>
      unfold tsubst_motive3
      repeat intro
      apply trans
      { aesop }
      { aesop }
    case tvar =>
      unfold tsubst_motive3
      repeat intro
      rename_i hb _ _ _ σ
      have hb1 := σ.tmap _ _ hb
      simp [SType.trename]
      trivial
    case tinstl =>
      unfold tsubst_motive3
      repeat intro
      rename_i hb _ _ Δ σ
      have hb1 := σ.tmap_inst _ _ hb
      simp [SType.trename]
      apply SSubtyp.tinstl
      trivial
    case tinstr =>
      unfold tsubst_motive3
      repeat intro
      rename_i hb _ _ Δ σ
      have hb1 := σ.tmap_inst _ _ hb
      simp [SType.trename]
      apply SSubtyp.tinstr
      trivial
    case boxed =>
      unfold tsubst_motive2 tsubst_motive3
      repeat intro
      simp [SType.trename]
      apply boxed
      aesop
    case label =>
      unfold tsubst_motive3
      repeat intro
      simp [SType.trename]
      apply label
      aesop
    case xforall =>
      unfold tsubst_motive1 tsubst_motive2 tsubst_motive3
      repeat intro
      simp [SType.trename]
      apply xforall
      { aesop }
      { rename_i ih _ _ _ σ
        apply ih ; try assumption
        apply TVarSubst.ext; trivial }
    case tforall =>
      unfold tsubst_motive1 tsubst_motive3
      repeat intro
      simp [SType.trename]
      apply tforall
      { aesop }
      { rename_i ih _ _ _ σ
        apply ih ; try assumption
        apply TVarSubst.text; trivial }
    case cforall =>
      unfold tsubst_motive1 tsubst_motive3
      repeat intro
      simp [SType.trename]
      apply cforall
      { rename_i ih _ _ _ σ
        apply ih ; try assumption
        apply TVarSubst.cext; trivial }

theorem CSubtyp.tsubst
  (h : CSubtyp Γ T1 T2)
  (σ : TVarSubst Γ f Δ) :
  CSubtyp Δ (T1.trename f) (T2.trename f) := by
  cases h
  case capt hc hs =>
    simp [CType.trename]
    apply CSubtyp.capt
    { apply hc.tsubst; trivial }
    { apply hs.tsubst; trivial }

theorem ESubtyp.tsubst
  (h : ESubtyp Γ E1 E2)
  (σ : TVarSubst Γ f Δ) :
  ESubtyp Δ (E1.trename f) (E2.trename f) := by
  cases h
  case exist hs =>
    simp [EType.trename]
    apply ESubtyp.exist
    { apply hs.tsubst
      apply σ.cext }
  case type hs =>
    simp [EType.trename]
    apply ESubtyp.type
    apply hs.tsubst; trivial

theorem ESubtyp.tnarrow
  (h : ESubtyp (Γ.tvar (TBinding.bound S)) E1 E2)
  (hs : SSubtyp Γ S' S) :
  ESubtyp (Γ.tvar (TBinding.bound S')) E1 E2 := by
  rw [<- EType.trename_id (E := E1), <- EType.trename_id (E := E2)]
  apply? ESubtyp.tsubst
  { apply? TVarSubst.narrow }

end Capless
