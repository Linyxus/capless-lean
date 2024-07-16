import Capless.Subtyping
import Capless.Renaming.Basic
import Capless.Renaming.Term.Subcapturing
namespace Capless

def SSubtyp.rename_motive1
  (Γ : Context n m k)
  (E1 : EType n m k)
  (E2 : EType n m k)
  : Prop :=
  ∀ {n'} (f : FinFun n n') (Δ : Context n' m k) (ρ : VarMap Γ f Δ),
  ESubtyp Δ (E1.rename f) (E2.rename f)

def SSubtyp.rename_motive2
  (Γ : Context n m k)
  (C1 : CType n m k)
  (C2 : CType n m k)
  : Prop :=
  ∀ {n'} (f : FinFun n n') (Δ : Context n' m k) (ρ : VarMap Γ f Δ),
  CSubtyp Δ (C1.rename f) (C2.rename f)

def SSubtyp.rename_motive3
  (Γ : Context n m k)
  (S1 : SType n m k)
  (S2 : SType n m k)
  : Prop :=
  ∀ {n'} (f : FinFun n n') (Δ : Context n' m k) (ρ : VarMap Γ f Δ),
  SSubtyp Δ (S1.rename f) (S2.rename f)

theorem SSubtyp.rename
  (h : SSubtyp Γ S1 S2)
  (ρ : VarMap Γ f Δ) :
  SSubtyp Δ (S1.rename f) (S2.rename f) := by
  apply SSubtyp.rec
    (motive_1 := fun Γ E1 E2 h => SSubtyp.rename_motive1 Γ E1 E2)
    (motive_2 := fun Γ C1 C2 h => SSubtyp.rename_motive2 Γ C1 C2)
    (motive_3 := fun Γ S1 S2 h => SSubtyp.rename_motive3 Γ S1 S2)
    (t := h) (ρ := ρ)
  case exist ih =>
    unfold SSubtyp.rename_motive1 SSubtyp.rename_motive2
    intros; intros
    simp [EType.rename]
    apply ESubtyp.exist
    rename_i ih _ _ _ _
    apply ih <;> try assumption
    apply VarMap.cext <;> trivial
  -- case existp_erase =>
  --   unfold SSubtyp.rename_motive1 SSubtyp.rename_motive2
  --   repeat intro
  --   simp [EType.rename]
  --   apply ESubtyp.existp_erase
  --   rename_i ih _ _ _ _
  --   apply ih <;> try assumption
  --   apply VarMap.cext <;> trivial
  case type ih =>
    unfold rename_motive1 rename_motive2
    repeat intro
    simp [EType.rename]
    apply ESubtyp.type
    aesop
  case capt =>
    unfold rename_motive2 rename_motive3
    repeat intro
    simp [CType.rename]
    apply CSubtyp.capt
    apply Subcapt.rename <;> assumption
    aesop
  case top =>
    unfold rename_motive3
    repeat intro
    simp [SType.rename]
    constructor
  case refl =>
    unfold rename_motive3
    repeat intro
    constructor
  case trans =>
    unfold rename_motive3
    repeat intro
    rename_i ih1 ih2 _ _ _ _
    apply trans <;> aesop
  case tvar =>
    unfold rename_motive3
    repeat intro
    simp [SType.rename]
    apply SSubtyp.tvar
    rename_i hb _ _ _ ρ
    have hb1 := ρ.tmap _ _ hb
    simp [TBinding.rename] at hb1
    assumption
  case tinstl =>
    unfold rename_motive3
    repeat intro
    simp [SType.rename]
    apply SSubtyp.tinstl
    rename_i hb _ _ _ ρ
    have hb1 := ρ.tmap _ _ hb
    simp [TBinding.rename] at hb1
    assumption
  case tinstr =>
    unfold rename_motive3
    repeat intro
    simp [SType.rename]
    apply SSubtyp.tinstr
    rename_i hb _ _ _ ρ
    have hb1 := ρ.tmap _ _ hb
    simp [TBinding.rename] at hb1
    assumption
  case boxed =>
    unfold rename_motive3
    repeat intro
    simp [SType.rename]
    apply SSubtyp.boxed
    aesop
  case xforall =>
    unfold rename_motive3 rename_motive1
    repeat intro
    simp [SType.rename]
    apply SSubtyp.xforall
    aesop
    rename_i ih _ _ _ _
    apply ih <;> try assumption
    apply VarMap.ext <;> trivial
  case cforall =>
    unfold rename_motive1 rename_motive3
    repeat intro
    simp [SType.rename]
    apply SSubtyp.cforall
    rename_i ih _ _ _ _
    apply ih
    apply VarMap.cext <;> trivial
  case tforall =>
    unfold rename_motive1 rename_motive3
    repeat intro
    simp [SType.rename]
    apply SSubtyp.tforall
    aesop
    rename_i ih1 ih2 _ _ _ _
    apply ih2 <;> try assumption
    apply VarMap.text <;> trivial

theorem CSubtyp.rename
  (h : CSubtyp Γ T1 T2)
  (ρ : VarMap Γ f Δ) :
  CSubtyp Δ (T1.rename f) (T2.rename f) := by
  cases h
  case capt hc hs =>
    simp [CType.rename]
    constructor
    apply Subcapt.rename <;> assumption
    apply SSubtyp.rename <;> assumption

theorem ESubtyp.rename
  (h : ESubtyp Γ E1 E2)
  (ρ : VarMap Γ f Δ) :
  ESubtyp Δ (E1.rename f) (E2.rename f) := by
  cases h
  case exist hc hs =>
    simp [EType.rename]
    constructor
    apply CSubtyp.rename <;> try assumption
    apply VarMap.cext; assumption
  -- case existp_erase hs =>
  --   simp [EType.rename]
  --   constructor
  --   apply CSubtyp.rename <;> try assumption
  --   apply VarMap.cext; assumption
  case type hc =>
    simp [EType.rename]
    constructor
    apply CSubtyp.rename <;> assumption

theorem CSubtyp.weaken
  (h : CSubtyp Γ E1 E2) :
  CSubtyp (Γ.var T) E1.weaken E2.weaken := by
  simp [CType.weaken]
  apply CSubtyp.rename
  { apply h }
  { apply VarMap.weaken }

end Capless
