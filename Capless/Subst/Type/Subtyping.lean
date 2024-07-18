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

theorem Context.cvar_tbound_tvar_inv'
  (he : Γ0 = Context.cvar Γ b)
  (hb : Context.TBound Γ0 X T) :
  ∃ T0, Context.TBound Γ X T0 ∧ T = T0.cweaken := by
  cases hb <;> try (solve | cases he)
  case there_cvar =>
    cases he
    rename_i E0 _
    exists E0

theorem Context.cvar_tbound_tvar_inv --TODO move
  (hb : Context.TBound (Context.cvar Γ b) X T) :
  ∃ T0, Context.TBound Γ X T0 ∧ T = T0.cweaken :=
  Context.cvar_tbound_tvar_inv' rfl hb

theorem SType.cweaken_trename {S : SType n m k} : --TODO move
  (S.trename f).cweaken = S.cweaken.trename f := by
  simp [cweaken, crename_trename_comm]

theorem SSubtyp.cweaken -- TODO: move weakening lemmas into separate package?
  (h : SSubtyp Γ S1 S2) :
  ∀ b, SSubtyp (Γ.cvar b) S1.cweaken S2.cweaken := by
  intro b
  simp [SType.cweaken]
  apply? SSubtyp.crename
  apply CVarMap.weaken

def TVarSubst.cext {Γ : Context n m k} -- TODO move
  (σ : TVarSubst Γ f Δ) :
  TVarSubst (Γ.cvar b) f (Δ.cvar b) := by
  constructor
  case map =>
    intros x T hb
    cases hb
    case there_cvar hb0 =>
      have h0 := σ.map _ _ hb0
      rw [<-CType.cweaken_trename]
      constructor
      exact h0
  case tmap =>
    intros X S hb
    have hb' := Context.cvar_tbound_tvar_inv hb
    obtain ⟨hb'',  hb''', heq⟩ := hb'
    cases hb''
    case bound S' =>
      have h0 := σ.tmap _ _ hb'''
      rw [heq] at hb
      simp [TBinding.cweaken, TBinding.crename] at heq
      rw [heq]
      have heq' : (S'.crename FinFun.weaken) = S'.cweaken := rfl
      rw [heq']
      rw [<-SType.cweaken_trename]
      have hb'' := h0.cweaken b
      simp [SType.cweaken, SType.crename] at *
      exact hb''
    case inst S' =>
      have h0 := σ.tmap_inst _ _ hb'''
      rw [heq] at hb
      simp [TBinding.cweaken, TBinding.crename] at heq
  case tmap_inst =>
    intros X S hb
    have hb' := Context.cvar_tbound_tvar_inv hb
    obtain ⟨hb'',  hb''', heq⟩ := hb'
    cases hb''
    case bound S' =>
      have h0 := σ.tmap _ _ hb'''
      rw [heq] at hb
      simp [TBinding.cweaken, TBinding.crename] at heq
    case inst S' =>
      have h0 := σ.tmap_inst _ _ hb'''
      rw [heq] at hb
      simp [TBinding.cweaken, TBinding.crename] at heq
      rw [heq]
      have heq' : (S'.crename FinFun.weaken) = S'.cweaken := rfl
      rw [heq']
      rw [<-SType.cweaken_trename]
      have hb'' := h0.cweaken b
      simp [SType.cweaken, SType.crename] at *
      exact hb''
  case cmap =>
    intros c b' hb
    cases hb
    case here => constructor
    case there_cvar x b' hb' =>
      have hb'' := σ.cmap _ _ hb'
      constructor
      exact hb''

def TVarSubst.ext {Γ : Context n m k} -- TODO move
  (σ : TVarSubst Γ f Δ)
  (T : CType n m k) :
  TVarSubst (Γ.var T) f (Δ.var (T.trename f)) := sorry

def TVarSubst.text {Γ : Context n m k} -- TODO move
  (σ : TVarSubst Γ f Δ)
  (T : TBinding n m k) :
  TVarSubst (Γ.tvar T) f.ext (Δ.tvar (T.trename f)) := sorry

lemma SSubtyp.tinstl' (h : SSubtyp Γ (SType.tvar X) S) : SSubtyp Δ S (SType.tvar X) := by -- TODO move
  sorry

theorem SSubtyp.tsubst
  (h : SSubtyp Γ S1 S2)
  (σ : TVarSubst Γ f Δ) :
  SSubtyp Δ (S1.trename f) (S2.trename f) := by
    apply SSubtyp.rec
      (motive_1 := fun Γ E1 E2 h => SSubtyp.tsubst_motive1 Γ E1 E2)
      (motive_2 := fun Γ C1 C2 h => SSubtyp.tsubst_motive2 Γ C1 C2)
      (motive_3 := fun Γ S1 S2 h => SSubtyp.tsubst_motive3 Γ S1 S2)
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
      apply SSubtyp.tinstl'
      trivial
    case tinstr =>
      unfold tsubst_motive3
      repeat intro
      rename_i hb _ _ Δ σ
      have hb1 := σ.tmap_inst _ _ hb
      simp [SType.trename]
      trivial
    case boxed =>
      unfold tsubst_motive2 tsubst_motive3
      repeat intro
      simp [SType.trename]
      apply boxed
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
  (h : CSubtyp Γ S1 S2)
  (σ : TVarSubst Γ f Δ) :
  CSubtyp Δ (S1.trename f) (S2.trename f) := by
  cases h
  case capt hc hs =>
    simp [CType.trename]
    apply CSubtyp.capt
    { apply! Subcapt.tsubst }
    { apply! SSubtyp.tsubst }

theorem ESubtyp.tsubst
  (h : ESubtyp Γ S1 S2)
  (σ : TVarSubst Γ f Δ) :
  ESubtyp Δ (S1.trename f) (S2.trename f) := sorry

theorem ESubtyp.tnarrow
  (h : ESubtyp (Γ.tvar (TBinding.bound S)) E1 E2)
  (hs : SSubtyp Γ S' S) :
  ESubtyp (Γ.tvar (TBinding.bound S')) E1 E2 := by
  rw [<- EType.trename_id (E := E1), <- EType.trename_id (E := E2)]
  apply? ESubtyp.tsubst
  { apply? TVarSubst.narrow }

end Capless
