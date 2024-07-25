import Capless.Tactics
import Capless.Subtyping
import Capless.Renaming.Basic
import Capless.Renaming.Type.Subcapturing
namespace Capless

def SSubtyp.trename_motive1
  (Γ : Context n m k)
  (E1 : EType n m k)
  (E2 : EType n m k)
  : Prop :=
  ∀ {m'} (f : FinFun m m') (Δ : Context n m' k) (ρ : TVarMap Γ f Δ),
  ESubtyp Δ (E1.trename f) (E2.trename f)

def SSubtyp.trename_motive2
  (Γ : Context n m k)
  (T1 : CType n m k)
  (T2 : CType n m k)
  : Prop :=
  ∀ {m'} (f : FinFun m m') (Δ : Context n m' k) (ρ : TVarMap Γ f Δ),
  CSubtyp Δ (T1.trename f) (T2.trename f)

def SSubtyp.trename_motive3
  (Γ : Context n m k)
  (S1 : SType n m k)
  (S2 : SType n m k)
  : Prop :=
  ∀ {m'} (f : FinFun m m') (Δ : Context n m' k) (ρ : TVarMap Γ f Δ),
  SSubtyp Δ (S1.trename f) (S2.trename f)

theorem SSubtyp.trename
  (h : SSubtyp Γ S1 S2)
  (ρ : TVarMap Γ f Δ) :
  SSubtyp Δ (S1.trename f) (S2.trename f) := by
  apply SSubtyp.rec
    (motive_1 := fun Γ E1 E2 h => SSubtyp.trename_motive1 Γ E1 E2)
    (motive_2 := fun Γ C1 C2 h => SSubtyp.trename_motive2 Γ C1 C2)
    (motive_3 := fun Γ S1 S2 h => SSubtyp.trename_motive3 Γ S1 S2)
    (t := h) (ρ := ρ)
  case exist =>
    unfold trename_motive1 trename_motive2
    repeat intro
    simp [EType.trename]
    apply ESubtyp.exist
    rename_i ih _ _ _ _
    apply ih; apply TVarMap.cext <;> trivial
  case type =>
    unfold trename_motive1 trename_motive2
    repeat intro
    simp [EType.trename]
    apply ESubtyp.type
    aesop
  case capt =>
    unfold trename_motive2 trename_motive3
    repeat intro
    simp [CType.trename]
    apply CSubtyp.capt
    apply Subcapt.trename <;> trivial
    aesop
  case top =>
    unfold trename_motive3
    repeat intro
    simp [SType.trename]
    apply SSubtyp.top
  case refl =>
    unfold trename_motive3
    repeat intro
    apply refl
  case trans =>
    unfold trename_motive3
    repeat intro
    apply trans <;> aesop
  case tvar =>
    unfold trename_motive3
    repeat intro
    simp [SType.trename]
    apply tvar
    rename_i hb _ _ _ ρ
    have hb1 := ρ.tmap _ _ hb
    simp [TBinding.trename] at hb1
    exact hb1
  case tinstl =>
    unfold trename_motive3
    repeat intro
    simp [SType.trename]
    apply tinstl
    rename_i hb _ _ _ ρ
    have hb1 := ρ.tmap _ _ hb
    simp [TBinding.trename] at hb1
    exact hb1
  case tinstr =>
    unfold trename_motive3
    repeat intro
    simp [SType.trename]
    apply tinstr
    rename_i hb _ _ _ ρ
    have hb1 := ρ.tmap _ _ hb
    simp [TBinding.trename] at hb1
    exact hb1
  case boxed =>
    unfold trename_motive2 trename_motive3
    repeat intro
    simp [SType.trename]
    apply boxed
    aesop
  case xforall =>
    unfold trename_motive1 trename_motive3
    repeat intro
    simp [SType.trename]
    apply xforall
    aesop
    rename_i ih2 _ _ _ _
    apply ih2; apply TVarMap.ext <;> trivial
  case tforall =>
    unfold trename_motive1 trename_motive3
    repeat intro
    simp [SType.trename]
    apply tforall
    aesop
    rename_i ih2 _ _ _ _
    apply ih2; apply TVarMap.text <;> trivial
  case cforall =>
    unfold trename_motive1 trename_motive3
    repeat intro
    simp [SType.trename]
    apply cforall
    rename_i ih2 _ _ _ _
    apply ih2; apply TVarMap.cext <;> trivial

theorem CSubtyp.trename
  (h : CSubtyp Γ T1 T2)
  (ρ : TVarMap Γ f Δ) :
  CSubtyp Δ (T1.trename f) (T2.trename f) := by
  cases h
  case capt hc hs =>
    simp [CType.trename]
    apply capt
    apply Subcapt.trename <;> trivial
    apply SSubtyp.trename <;> trivial

theorem ESubtyp.trename
  (h : ESubtyp Γ E1 E2)
  (ρ : TVarMap Γ f Δ) :
  ESubtyp Δ (E1.trename f) (E2.trename f) := by
  cases h
  case exist hs =>
    simp [EType.trename]
    apply ESubtyp.exist
    apply CSubtyp.trename <;> try trivial
    apply TVarMap.cext; trivial
  case type hs =>
    simp [EType.trename]
    apply ESubtyp.type
    apply CSubtyp.trename <;> trivial

end Capless
