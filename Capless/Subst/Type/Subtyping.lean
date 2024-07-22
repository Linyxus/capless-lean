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

theorem Context.tvar_tbound_inv' -- TODO move
  (he1 : Γ0 = Γ.tvar p)
  (hb : Context.TBound Γ0 X0 b) :
  (X0 = 0 ∧ b = p.tweaken) ∨
  (∃ b0 X, Context.TBound Γ X b0 ∧ b = b0.tweaken ∧ X0 = (Fin.succ X)) := by
  cases X0 using Fin.cases
  case zero =>
    left
    cases hb <;> try (solve | cases he1 | cases he2 | aesop)
  case succ n =>
    right
    rw [he1] at hb
    apply Context.tvar_tbound_succ_inv at hb
    aesop

theorem Context.tvar_tbound_inv -- TODO move
  (hb : Context.TBound (Γ.tvar p) X b) :
  (X = 0 ∧ b = p.tweaken) ∨
  (∃ b0 X0, Context.TBound Γ X0 b0 ∧ b = b0.tweaken ∧ X = (Fin.succ X0)) :=
  Context.tvar_tbound_inv' rfl hb

theorem SType.cweaken_trename {S : SType n m k} : --TODO move
  (S.trename f).cweaken = S.cweaken.trename f := by
  simp [cweaken, crename_trename_comm]

theorem SType.weaken_trename {S : SType n m k} : --TODO move
  (S.trename f).weaken = S.weaken.trename f := by
  simp [weaken, SType.trename_rename_comm]

theorem SType.tweaken_trename {S : SType n m k} :
  (S.trename f).tweaken = S.tweaken.trename f.ext := by
  simp [tweaken, trename_trename, FinFun.comp_weaken]

theorem SSubtyp.cweaken -- TODO: move weakening lemmas into separate package?
  (h : SSubtyp Γ S1 S2) :
  ∀ b, SSubtyp (Γ.cvar b) S1.cweaken S2.cweaken := by
  intro b
  simp [SType.cweaken]
  apply? SSubtyp.crename
  apply CVarMap.weaken

theorem SSubtyp.weaken
  (h : SSubtyp Γ S1 S2) :
  ∀ b, SSubtyp (Γ.var b) S1.weaken S2.weaken := by
  intro b
  simp [SType.weaken]
  apply? SSubtyp.rename
  apply VarMap.weaken

@[simp]
lemma TBinding.tweaken_bound: (TBinding.bound T).tweaken = TBinding.bound (T.tweaken) := by aesop

@[simp]
lemma TBinding.tweaken_inst: (TBinding.inst T).tweaken = TBinding.inst (T.tweaken) := by aesop

@[simp]
lemma TBinding.cweaken_bound: (TBinding.bound T).cweaken = TBinding.bound (T.cweaken) := by aesop

@[simp]
lemma TBinding.cweaken_inst: (TBinding.inst T).cweaken = TBinding.inst (T.cweaken) := by aesop

@[simp]
lemma TBinding.weaken_bound: (TBinding.bound T).weaken = TBinding.bound (T.weaken) := by aesop

@[simp]
lemma TBinding.weaken_inst: (TBinding.inst T).weaken = TBinding.inst (T.weaken) := by aesop

lemma FinFun.comp_succ {f : FinFun n n'}: Fin.succ ∘ f = (FinFun.ext f) ∘ Fin.succ := by --TODO move
  funext i
  cases n
  case zero =>
    aesop
  case succ n =>
    simp [FinFun.ext]

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
      simp at heq
      rw [heq]
      rw [<-SType.cweaken_trename]
      have hb'' := h0.cweaken b
      simp [SType.cweaken, SType.crename] at *
      exact hb''
    case inst S' =>
      simp at heq
  case tmap_inst =>
    intros X S hb
    have hb' := Context.cvar_tbound_tvar_inv hb
    obtain ⟨hb'',  hb''', heq⟩ := hb'
    cases hb''
    case bound S' =>
      simp at heq
    case inst S' =>
      have h0 := σ.tmap_inst _ _ hb'''
      simp at heq
      rw [heq]
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
  TVarSubst (Γ.var T) f (Δ.var (T.trename f)) := by
  constructor
  case map =>
    intros x T hb
    cases hb
    case here =>
      rw [<-CType.weaken_trename]
      constructor
    case there_var hb0 =>
      have h0 := σ.map _ _ hb0
      rw [<-CType.weaken_trename]
      constructor
      exact h0
  case tmap =>
    intros X S hb
    have hb' := Context.var_tbound_inv hb
    obtain ⟨hb'',  hb''', heq⟩ := hb'
    cases hb''
    case bound S' =>
      have h0 := σ.tmap _ _ hb'''
      simp at heq
      rw [heq]
      rw [<-SType.weaken_trename]
      have hb'' := h0.weaken (T.trename f)
      simp [SType.weaken, SType.rename] at *
      exact hb''
    case inst S' =>
      simp at heq
  case tmap_inst =>
    intros X S hb
    have hb' := Context.var_tbound_inv hb
    obtain ⟨hb'',  hb''', heq⟩ := hb'
    cases hb''
    case bound S' =>
      simp at heq
    case inst S' =>
      have h0 := σ.tmap_inst _ _ hb'''
      simp at heq
      rw [heq]
      rw [<-SType.weaken_trename]
      have hb'' := h0.weaken (T.trename f)
      simp [SType.weaken, SType.rename] at *
      exact hb''
  case cmap =>
    intros c b' hb
    cases hb
    case there_var x b' hb' =>
      have hb'' := σ.cmap _ _ hb'
      constructor
      exact hb''

def TVarSubst.text {Γ : Context n m k} -- TODO move
  (σ : TVarSubst Γ f Δ)
  (T : TBinding n m k) :
  TVarSubst (Γ.tvar T) f.ext (Δ.tvar (T.trename f)) := by
    constructor
    case map =>
      intros x T hb
      cases hb
      case there_tvar hb0 =>
        have h0 := σ.map _ _ hb0
        rw [<-CType.tweaken_trename]
        constructor
        exact h0
    case tmap =>
      intros X S hb
      have hb' := Context.tvar_tbound_inv hb
      cases hb'
      case inl hb' =>
        obtain ⟨ hz , hbnd ⟩ := hb'
        rw [hz, hbnd] at hb
        rw [hz]
        simp [FinFun.ext]
        apply SSubtyp.tvar
        cases T
        case bound T =>
          simp at hbnd
          rw [hbnd]
          rw [<-SType.tweaken_trename]
          constructor
        case inst T =>
          simp at hbnd
      case inr hb' =>
        obtain ⟨T', X',  hb', heq, heq'⟩ := hb'
        rw [heq'] at hb
        cases T'
        case bound T' =>
          simp at heq
          rw [heq,heq']
          have h0 := σ.tmap _ _ hb'
          apply (@SSubtyp.tweaken _ _ _ _  _ _ (T.trename f)) at h0
          simp [SType.tweaken, SType.trename, SType.trename_trename,FinFun.ext,FinFun.weaken,FinFun.comp_succ] at *
          trivial
        case inst S' =>
          simp at heq
    case tmap_inst =>
      intros X S hb
      have hb' := Context.tvar_tbound_inv hb
      cases hb'
      case inl hb' =>
        obtain ⟨ hz , hbnd ⟩ := hb'
        rw [hz, hbnd] at hb
        rw [hz]
        simp [FinFun.ext]
        apply SSubtyp.tinstr
        cases T
        case bound T =>
          simp at hbnd
        case inst T =>
          simp at hbnd
          rw [hbnd]
          rw [<-SType.tweaken_trename]
          constructor
      case inr hb' =>
        obtain ⟨T', X',  hb', heq, heq'⟩ := hb'
        rw [heq'] at hb
        cases T'
        case bound T' =>
          simp at heq
        case inst S' =>
          simp at heq
          rw [heq,heq']
          have h0 := σ.tmap_inst _ _ hb'
          apply (@SSubtyp.tweaken _ _ _ _  _ _ (T.trename f)) at h0
          simp [SType.tweaken, SType.trename, SType.trename_trename,FinFun.ext,FinFun.weaken,FinFun.comp_succ] at *
          trivial
    case cmap =>
      intros c b' hb
      cases hb
      case there_tvar x hb' =>
        have hb'' := σ.cmap _ _ hb'
        constructor
        exact hb''

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
