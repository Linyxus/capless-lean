import Capless.Basic
import Capless.Context
import Capless.CaptureSet
import Capless.Type.Basic
import Capless.Typing
import Capless.Typing.Basic
import Capless.Weakening.Subtyping
import Capless.Weakening.Typing
import Capless.Inversion.Context
namespace Capless

structure VarSubst (Γ : Context n m k) (f : FinFun n n') (Δ : Context n' m k) where
  map : ∀ x E, Γ.Bound x E -> Typed Δ (Term.var (f x)) (EType.type (E.rename f)) {x=f x}
  tmap : ∀ X b, Γ.TBound X b -> Δ.TBound X (b.rename f)
  cmap : ∀ c b, Γ.CBound c b -> Δ.CBound c (b.rename f)
  lmap : ∀ l S, Γ.LBound l S -> Δ.LBound (f l) (S.rename f)

structure TVarSubst (Γ : Context n m k) (f : FinFun m m') (Δ : Context n m' k) where
  map : ∀ x E, Γ.Bound x E -> Δ.Bound x (E.trename f)
  tmap : ∀ X S, Γ.TBound X (TBinding.bound S) ->
    SSubtyp Δ (SType.tvar (f X)) (S.trename f)
  tmap_inst : ∀ X S, Γ.TBound X (TBinding.inst S) ->
    Δ.TBound (f X) (TBinding.inst (S.trename f))
  cmap : ∀ c b, Γ.CBound c b -> Δ.CBound c b
  lmap : ∀ l S, Γ.LBound l S -> Δ.LBound l (S.trename f)

structure CVarSubst (Γ : Context n m k) (f : FinFun k k') (Δ : Context n m k') where
  map : ∀ x E, Γ.Bound x E -> Δ.Bound x (E.crename f)
  tmap : ∀ X b, Γ.TBound X b -> Δ.TBound X (b.crename f)
  cmap : ∀ c C, Γ.CBound c (CBinding.inst C) ->
    Δ.CBound (f c) (CBinding.inst (C.crename f))
  lmap : ∀ l S, Γ.LBound l S -> Δ.LBound l (S.crename f)

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
      rw [<- CType.weaken_rename]
      apply Typed.bound_typing
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
  case lmap =>
    intros l S hb
    cases hb
    case there_var hb0 =>
      have hb1 := σ.lmap _ _ hb0
      rw [<- SType.weaken_rename]
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
  case lmap =>
    intros l S hb
    cases hb
    case there_tvar hb0 =>
      have hb1 := σ.lmap _ _ hb0
      rw [SType.tweaken_rename]
      constructor; aesop

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
  case lmap =>
    intro l S hb
    cases hb
    case there_cvar hb0 =>
      have hb1 := σ.lmap _ _ hb0
      rw [SType.cweaken_rename_comm]
      constructor; aesop

def TVarSubst.cext {Γ : Context n m k}
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
      rw [<-SType.cweaken_trename,<-TBinding.cweaken_inst]
      constructor
      trivial
  case cmap =>
    intros c b' hb
    cases hb
    case here => constructor
    case there_cvar x b' hb' =>
      have hb'' := σ.cmap _ _ hb'
      constructor
      exact hb''
  case lmap =>
    intros l S hb
    cases hb
    case there_cvar hb0 =>
      have hb' := σ.lmap _ _ hb0
      rw [<- SType.cweaken_trename]
      constructor
      assumption

def TVarSubst.ext {Γ : Context n m k}
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
      rw [<-SType.weaken_trename,<-TBinding.weaken_inst]
      constructor
      trivial
  case cmap =>
    intros c b' hb
    cases hb
    case there_var x b' hb' =>
      have hb'' := σ.cmap _ _ hb'
      constructor
      exact hb''
  case lmap =>
    intros l S hb
    cases hb
    case there_var hb0 =>
      have hb' := σ.lmap _ _ hb0
      rw [<- SType.weaken_trename]
      constructor
      assumption

def TVarSubst.text {Γ : Context n m k}
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
          simp [FinFun.ext]
          rw [<-SType.tweaken_trename, <-TBinding.tweaken_inst]
          constructor
          trivial
    case cmap =>
      intros c b' hb
      cases hb
      case there_tvar x hb' =>
        have hb'' := σ.cmap _ _ hb'
        constructor
        exact hb''
    case lmap =>
      intros l S hb
      cases hb
      case there_tvar hb0 =>
        have hb' := σ.lmap _ _ hb0
        rw [<- SType.tweaken_trename]
        constructor
        assumption

def CVarSubst.ext {Γ : Context n m k}
  (σ : CVarSubst Γ f Δ)
  (T : CType n m k) :
  CVarSubst (Γ.var T) f (Δ.var (T.crename f)) := by
  constructor
  case map =>
    intros x T hb
    cases hb
    case here =>
      rw [<-CType.weaken_crename]
      constructor
    case there_var hb0 =>
      have h0 := σ.map _ _ hb0
      rw [<-CType.weaken_crename]
      constructor
      exact h0
  case tmap =>
    intros X S hb
    cases hb
    case there_var b hb =>
      rw [<-TBinding.weaken_crename]
      have hb' := σ.tmap _ _ hb
      constructor
      trivial
  case cmap =>
    intros c b' hb
    have hb' := Context.var_cbound_inv hb
    obtain ⟨b,  hb', heq⟩ := hb'
    cases b
    cases heq
    case inst b' =>
      simp at heq
      rw [heq]
      rw [<-CaptureSet.weaken_crename]
      rw [<-CBinding.weaken_inst]
      have hb'' := σ.cmap _ _ hb'
      constructor
      trivial
  case lmap =>
    intros l S hb
    cases hb
    case there_var hb0 =>
      have hb' := σ.lmap _ _ hb0
      rw [<- SType.weaken_crename]
      constructor
      assumption

def CVarSubst.text {Γ : Context n m k}
  (σ : CVarSubst Γ f Δ) :
  CVarSubst (Γ.tvar T) f (Δ.tvar (T.crename f)) := by
    constructor
    case map =>
      intros x T hb
      cases hb
      case there_tvar hb0 =>
        have h0 := σ.map _ _ hb0
        rw [<-CType.tweaken_crename]
        constructor
        exact h0
    case tmap =>
      intros X S hb
      cases hb
      case here =>
        rw [<-TBinding.tweaken_crename]
        constructor
      case there_tvar X b hb =>
        have h0 := σ.tmap _ _ hb
        rw [<-TBinding.tweaken_crename]
        constructor
        trivial
    case cmap =>
      intros c b' hb
      cases hb
      case there_tvar x hb' =>
        have hb'' := σ.cmap _ _ hb'
        constructor
        trivial
    case lmap =>
      intros l S hb
      cases hb
      case there_tvar hb0 =>
        have hb' := σ.lmap _ _ hb0
        rw [<- SType.tweaken_crename]
        constructor
        assumption

def CVarSubst.cext {Γ : Context n m k}
  (σ : CVarSubst Γ f Δ) :
  CVarSubst (Γ.cvar b) f.ext (Δ.cvar (b.crename f)) := by
  constructor
  case map =>
    intros x T hb
    cases hb
    case there_cvar hb0 =>
      have h0 := σ.map _ _ hb0
      rw [<-CType.cweaken_crename]
      constructor
      exact h0
  case tmap =>
    intros X S hb
    cases hb
    case there_cvar b hb' =>
    have h0 := σ.tmap _ _ hb'
    rw [<-TBinding.cweaken_crename]
    constructor
    trivial
  case cmap =>
    intros c C hb
    have hb' := Context.cvar_cbound_inv hb
    cases hb'
    case inl hb' =>
      obtain ⟨ hz , hbnd ⟩ := hb'
      rw [hz, hbnd] at hb
      rw [hz]
      simp [FinFun.ext]
      cases b
      cases hbnd
      case inst C' =>
        simp at hbnd
        rw [hbnd]
        rw [<-CaptureSet.cweaken_crename,<-CBinding.cweaken_inst]
        constructor
    case inr hb' =>
      obtain ⟨b', X,  hb', heq, heq'⟩ := hb'
      rw [heq'] at hb
      rw [heq']
      cases b'
      cases heq
      case inst C' =>
        simp at heq
        rw [heq]
        have h0 := σ.cmap _ _ hb'
        simp [FinFun.ext]
        rw [<-CaptureSet.cweaken_crename,<-CBinding.cweaken_inst]
        constructor
        trivial
  case lmap =>
    intros l S hb
    cases hb
    case there_cvar hb0 =>
      have hb' := σ.lmap _ _ hb0
      rw [<- SType.cweaken_crename]
      constructor
      assumption

def VarSubst.open
  (hx : Typed Γ (Term.var x) (EType.type T) Cx) :
  VarSubst (Γ.var T) (FinFun.open x) Γ := by
  constructor
  case map =>
    intro x P hb
    cases hb
    case here =>
      simp [FinFun.open]
      simp [CType.weaken, CType.rename_rename, FinFun.open_comp_weaken]
      simp [CType.rename_id]
      apply Typed.precise_cv; trivial
    case there_var hb0 =>
      simp [FinFun.open]
      simp [CType.weaken, CType.rename_rename, FinFun.open_comp_weaken]
      simp [CType.rename_id]
      apply Typed.bound_typing
      trivial
  case tmap =>
    intro X b hb
    cases hb
    case there_var hb0 =>
      simp [TBinding.weaken, TBinding.rename_rename, FinFun.open_comp_weaken]
      simp [TBinding.rename_id]
      trivial
  case cmap =>
    intro c b hb
    cases hb
    case there_var hb0 =>
      simp [CBinding.weaken, CBinding.rename_rename, FinFun.open_comp_weaken]
      simp [CBinding.rename_id]
      trivial
  case lmap =>
    intro l S hb
    cases hb
    case there_var hb0 =>
      simp [SType.weaken, SType.rename_rename, FinFun.open_comp_weaken]
      simp [SType.rename_id]
      trivial

def VarSubst.narrow
  (hs : CSubtyp Γ T' T) :
  VarSubst (Γ.var T) FinFun.id (Γ.var T') := by
  constructor
  case map =>
    intro x Q hb
    cases hb
    case here =>
      simp [FinFun.id]
      simp [CType.rename_id]
      apply Typed.sub
      apply Typed.bound_typing; constructor
      apply Subcapt.refl
      apply ESubtyp.type
      apply hs.weaken
    case there_var hb0 =>
      simp [FinFun.id]
      simp [CType.rename_id]
      apply Typed.bound_typing
      constructor
      trivial
  case tmap =>
    intro X b hb
    cases hb
    case there_var hb0 =>
      simp [TBinding.rename_id]
      constructor; trivial
  case cmap =>
    intro c b hb
    cases hb
    case there_var hb0 =>
      simp [CBinding.rename_id]
      constructor; trivial
  case lmap =>
    intro l S hb
    cases hb
    case there_var hb0 =>
      simp [SType.rename_id]
      constructor; trivial

def TVarSubst.narrow
  (hs : SSubtyp Γ S' S) :
  TVarSubst
    (Γ.tvar (TBinding.bound S))
    FinFun.id
    (Γ.tvar (TBinding.bound S')) := by
  constructor
  case map =>
    intro x T hb
    simp [CType.trename_id]
    cases hb
    constructor
    trivial
  case tmap =>
    intro X S hb
    cases X using Fin.cases
    case zero =>
      cases hb
      simp [SType.trename_id, FinFun.id]
      apply SSubtyp.trans
      { apply SSubtyp.tvar
        { constructor } }
      { apply! SSubtyp.tweaken }
    case succ X0 =>
      simp [FinFun.id, SType.trename_id]
      have ⟨b0, hb0, he0⟩ := Context.tvar_tbound_succ_inv hb
      cases b0
      case bound =>
        simp [TBinding.tweaken, TBinding.trename] at he0
        subst_vars
        rw [<- SType.tvar_tweaken_succ]
        apply SSubtyp.tweaken
        apply! SSubtyp.tvar
      case inst => simp [TBinding.tweaken, TBinding.trename] at he0
  case tmap_inst =>
    intro X S hb
    simp [FinFun.id, SType.trename_id]
    have ⟨X0, S0, hb0, he1, he2⟩ := Context.tbound_tbound_inst_inv hb
    subst_vars
    have h : (TBinding.inst S0).tweaken = TBinding.inst (S0.tweaken) := by
      simp [TBinding.tweaken, TBinding.trename, SType.tweaken]
    rw [<- h]
    constructor
    trivial
  case cmap =>
    intro c b hb
    cases hb
    constructor
    trivial
  case lmap =>
    intro l S hb
    simp [SType.trename_id]
    cases hb
    constructor
    assumption

def TVarSubst.open :
  TVarSubst
    (Γ.tvar (TBinding.bound (SType.tvar X)))
    (FinFun.open X)
    Γ :=
  { map := fun x E hb => by
      cases hb
      case there_tvar hb0 =>
        simp [CType.tweaken, CType.trename_trename, FinFun.open_comp_weaken]
        simp [CType.trename_id]
        trivial
  , tmap := fun Y S hb => by
      cases Y using Fin.cases
      case zero =>
        cases hb
        simp [FinFun.open, SType.trename_trename, FinFun.open_comp_weaken]
        simp [SType.trename_id]
        constructor
      case succ =>
        have ⟨b0, hb0, he0⟩ := Context.tvar_tbound_succ_inv hb
        cases b0
        case bound =>
          simp [TBinding.tweaken, TBinding.trename] at he0
          subst_vars
          simp [SType.trename_trename, FinFun.open_comp_weaken, SType.trename_id, FinFun.open]
          apply! SSubtyp.tvar
        case inst =>
          simp [TBinding.tweaken, TBinding.trename] at he0
  , tmap_inst := fun Y S hb => by
      cases Y using Fin.cases
      case zero => cases hb
      case succ Y0 =>
        have ⟨X0, S0, hb0, he1, he2⟩ := Context.tbound_tbound_inst_inv hb
        subst_vars
        simp [SType.tweaken, SType.trename_trename, FinFun.open_comp_weaken, SType.trename_id, FinFun.open]
        rw [Fin.succ_inj] at he2
        subst_vars
        trivial
  , cmap := fun c b hb => by
      cases hb
      trivial
  , lmap := fun l S hb => by
      cases hb
      simp [SType.tweaken, SType.trename_trename, FinFun.open_comp_weaken, SType.trename_id, FinFun.open]
      assumption
  }

def CVarSubst.open :
  CVarSubst
    (Γ.cvar CBinding.bound)
    (FinFun.open c)
    Γ := by
  constructor
  case map =>
    intro x T hb
    cases hb
    simp [CType.cweaken, CType.crename_crename, FinFun.open_comp_weaken]
    simp [CType.crename_id]
    trivial
  case tmap =>
    intro X b hb
    cases hb
    simp [TBinding.cweaken, TBinding.crename_crename, FinFun.open_comp_weaken]
    simp [TBinding.crename_id]
    trivial
  case cmap =>
    intro c b hb
    have ⟨c0, C0, he1, he2, hb0⟩ := Context.cvar_bound_cvar_inst_inv hb
    subst_vars
    simp [FinFun.open, CaptureSet.cweaken]
    simp [CaptureSet.crename_crename]
    simp [FinFun.open_comp_weaken]
    simp [CaptureSet.crename_id]
    trivial
  case lmap =>
    intro l S hb
    cases hb
    simp [SType.cweaken, SType.crename_crename, FinFun.open_comp_weaken]
    simp [SType.crename_id]
    trivial

def CVarSubst.instantiate {Γ : Context n m k} :
  CVarSubst
    (Γ.cvar CBinding.bound)
    FinFun.id
    (Γ.cvar (CBinding.inst C)) := by
  constructor
  case map =>
    intro x T hb
    cases hb
    simp [CType.crename_id]
    constructor; trivial
  case tmap =>
    intro X b hb
    cases hb
    simp [TBinding.crename_id]
    constructor; trivial
  case cmap =>
    intro c C hb
    simp [FinFun.id, CaptureSet.crename_id]
    have ⟨c0, C0, he1, he2, hb0⟩ := Context.cvar_bound_cvar_inst_inv hb
    subst_vars
    have heq : (CBinding.inst C0).cweaken = CBinding.inst (C0.cweaken) := by
      simp [CBinding.cweaken, CBinding.crename, CaptureSet.cweaken]
    rw [<- heq]
    constructor
    trivial
  case lmap =>
    intro l S hb
    cases hb
    simp [SType.crename_id]
    constructor; trivial

-- structure OmniMap (n m k n' m' k' : Nat) where
--   map : FinFun n n'
--   tmap : FinFun m m'
--   cmap : FinFun k k'

-- structure OmniSubst (Γ : Context n m k) (f : OmniMap n m k n' m' k') (Δ : Context n' m' k') where

end Capless
