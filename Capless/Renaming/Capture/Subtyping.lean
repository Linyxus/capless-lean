import Capless.Tactics
import Capless.Subtyping
import Capless.Renaming.Basic
import Capless.Renaming.Capture.Subcapturing
namespace Capless

def SSubtyp.crename_motive1
  (Γ : Context n m k)
  (E1 : EType n m k)
  (E2 : EType n m k)
  : Prop :=
  ∀ {k'} (f : FinFun k k') (Δ : Context n m k') (ρ : CVarMap Γ f Δ),
  ESubtyp Δ (E1.crename f) (E2.crename f)

def SSubtyp.crename_motive2
  (Γ : Context n m k)
  (C1 : CType n m k)
  (C2 : CType n m k)
  : Prop :=
  ∀ {k'} (f : FinFun k k') (Δ : Context n m k') (ρ : CVarMap Γ f Δ),
  CSubtyp Δ (C1.crename f) (C2.crename f)

def SSubtyp.crename_motive3
  (Γ : Context n m k)
  (S1 : SType n m k)
  (S2 : SType n m k)
  : Prop :=
  ∀ {k'} (f : FinFun k k') (Δ : Context n m k') (ρ : CVarMap Γ f Δ),
  SSubtyp Δ (S1.crename f) (S2.crename f)

theorem SSubtyp.crename
  (h : SSubtyp Γ S1 S2)
  (ρ : CVarMap Γ f Δ) :
  SSubtyp Δ (S1.crename f) (S2.crename f) := by
  apply SSubtyp.rec
    (motive_1 := fun Γ E1 E2 h => SSubtyp.crename_motive1 Γ E1 E2)
    (motive_2 := fun Γ C1 C2 h => SSubtyp.crename_motive2 Γ C1 C2)
    (motive_3 := fun Γ S1 S2 h => SSubtyp.crename_motive3 Γ S1 S2)
    (t := h) (ρ := ρ)
  case exist =>
    unfold SSubtyp.crename_motive1 SSubtyp.crename_motive2
    repeat intro
    simp [EType.crename]
    apply ESubtyp.exist
    rename_i ih _ _ _ _
    apply ih; try assumption
    apply CVarMap.cext <;> trivial
  case type =>
    unfold crename_motive2 crename_motive1
    repeat intro
    simp [EType.crename]
    apply ESubtyp.type
    aesop
  case capt =>
    unfold crename_motive3 crename_motive2
    repeat intro
    simp [CType.crename]
    apply CSubtyp.capt
    apply Subcapt.crename <;> aesop
    aesop
  case top =>
    unfold crename_motive3
    repeat intro
    simp [SType.crename]
    apply SSubtyp.top
  case refl =>
    unfold crename_motive3
    repeat intro
    constructor
  case trans =>
    unfold crename_motive3
    repeat intro
    apply SSubtyp.trans
    aesop
    aesop
  case tvar =>
    unfold crename_motive3
    repeat intro
    simp [SType.crename]
    apply SSubtyp.tvar
    rename_i hb _ _ _ ρ
    have hb1 := ρ.tmap _ _ hb
    simp [TBinding.crename] at hb1
    trivial
  case tinstl =>
    unfold crename_motive3
    repeat intro
    simp [SType.crename]
    apply SSubtyp.tinstl
    rename_i hb _ _ _ ρ
    have hb1 := ρ.tmap _ _ hb
    simp [TBinding.crename] at hb1
    assumption
  case tinstr =>
    unfold crename_motive3
    repeat intro
    simp [SType.crename]
    apply SSubtyp.tinstr
    rename_i hb _ _ _ ρ
    have hb1 := ρ.tmap _ _ hb
    simp [TBinding.crename] at hb1
    assumption
  case boxed =>
    unfold crename_motive3 crename_motive2
    repeat intro
    simp [SType.crename]
    apply SSubtyp.boxed
    aesop
  case label =>
    unfold crename_motive3
    repeat intro
    simp [SType.crename]
    apply SSubtyp.label
    aesop
  case xforall =>
    unfold crename_motive1 crename_motive3
    repeat intro
    simp [SType.crename]
    apply SSubtyp.xforall
    aesop
    rename_i ih _ _ _ _
    apply ih; try assumption
    apply CVarMap.ext <;> trivial
  case tforall =>
    unfold crename_motive1 crename_motive3
    repeat intro
    simp [SType.crename]
    apply SSubtyp.tforall
    aesop
    rename_i ih1 ih2 _ _ _ _
    apply ih2 <;> try assumption
    apply CVarMap.text <;> trivial
  case cforall =>
    unfold crename_motive1 crename_motive3
    repeat intro
    simp [SType.crename]
    apply SSubtyp.cforall
    rename_i ih _ _ _ _
    apply ih
    apply CVarMap.cext <;> trivial

theorem CSubtyp.crename
  (h : CSubtyp Γ C1 C2)
  (ρ : CVarMap Γ f Δ) :
  CSubtyp Δ (C1.crename f) (C2.crename f) := by
  cases h
  case capt hc hs =>
    simp [CType.crename]
    apply capt
    apply Subcapt.crename <;> aesop
    apply SSubtyp.crename <;> aesop

theorem ESubtyp.crename
  (h : ESubtyp Γ E1 E2)
  (ρ : CVarMap Γ f Δ) :
  ESubtyp Δ (E1.crename f) (E2.crename f) := by
  cases h
  case exist hc =>
    simp [EType.crename]
    apply ESubtyp.exist
    apply CSubtyp.crename; trivial
    apply ρ.cext
  case type =>
    simp [EType.crename]
    apply ESubtyp.type
    apply CSubtyp.crename <;> trivial

end Capless
