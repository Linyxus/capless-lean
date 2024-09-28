import Capless.Store
import Capless.Type
import Capless.Reduction
import Capless.Inversion.Typing
import Capless.Inversion.Lookup
import Capless.Renaming.Term.Subtyping
import Capless.Renaming.Type.Subtyping
import Capless.Renaming.Capture.Subtyping
import Capless.Subst.Term.Typing
import Capless.Subst.Type.Typing
import Capless.Subst.Capture.Typing
import Capless.Weakening.TypedCont
import Capless.Tactics
import Capless.WellScoped.Basic
namespace Capless

inductive Preserve : Context n m k -> EType n m k -> State n' m' k' -> Prop where
| mk :
  TypedState state Γ E ->
  Preserve Γ E state
| mk_weaken :
  TypedState state (Γ.var P) E.weaken ->
  Preserve Γ E state
| mk_tweaken :
  TypedState state (Γ.tvar b) E.tweaken ->
  Preserve Γ E state
| mk_cweaken :
  TypedState state (Γ.cvar b) E.cweaken ->
  Preserve Γ E state

theorem value_typing_widen
  (hv : Typed Γ v (EType.type (S^C)) Cv)
  (hs : Γ ⊢ (S^C1) <: (S'^C2)) :
  Typed Γ v (S'^C) Cv := by
    cases hs
    apply Typed.sub
    easy
    apply Subcapt.refl
    constructor
    constructor
    apply Subcapt.refl
    easy

theorem preservation
  (hr : Reduce state state')
  (ht : TypedState state Γ E) :
  Preserve Γ E state' := by
  cases hr
  case apply hl =>
    cases ht
    case mk hs hsc ht hc =>
      have hg := TypedStore.is_tight hs
      have ⟨T0, Cf, F0, E0, hx, hy, he1, hs1⟩:= Typed.app_inv ht
      have ⟨Sv, Cv, Cv0, hv, hbx, hvs⟩ := Store.lookup_inv_typing hl hs hx
      have hv' := value_typing_widen hv hvs
      have ⟨hcfs, hcft⟩ := Typed.canonical_form_lam hg hv'
      constructor
      constructor
      { easy }
      { apply Typed.sub
        { apply Typed.open (h := hcft)
          exact hy }
        { apply Subcapt.refl }
        { subst he1
          easy } }
      { have h1 := Typed.app_inv_capt ht
        have h2 := WellScoped.subcapt hsc h1
        simp [CaptureSet.open]
        simp [FinFun.open, CaptureSet.weaken, CaptureSet.rename_rename]
        simp [FinFun.open_comp_weaken, CaptureSet.rename_id]
        cases h2; rename_i h2 h3
        apply WellScoped.union
        { apply WellScoped.var_inv
          exact h2; easy }
        { easy } }
      { easy }
  case tapply hl =>
    cases ht
    case mk hs hsc ht hc =>
      have hg := TypedStore.is_tight hs
      have ⟨Cf, F, E0, hx, he0, hs0⟩ := Typed.tapp_inv ht
      have ⟨Sv, Cv, Cv0, hv, hbx, hvs⟩ := Store.lookup_inv_typing hl hs hx
      have hv' := value_typing_widen hv hvs
      have ⟨hs1, hft⟩ := Typed.canonical_form_tlam hg hv'
      constructor
      constructor
      { easy }
      { apply Typed.sub
        { apply Typed.topen (h := hft) }
        { apply Subcapt.refl }
        { subst he0
          easy } }
      { have h1 := Typed.tapp_inv_capt ht
        have h2 := WellScoped.subcapt hsc h1
        apply WellScoped.var_inv
        exact h2
        easy }
      easy
  case capply hl =>
    cases ht
    case mk hs hsc ht hc =>
      have hg := TypedStore.is_tight hs
      have ⟨Cf, F, E0, hx, he1, hs1⟩ := Typed.capp_inv ht
      have ⟨Sv, Cv, Cv0, hv, hbx, hvs⟩ := Store.lookup_inv_typing hl hs hx
      have hv' := value_typing_widen hv hvs
      have hct := Typed.canonical_form_clam hg hv'
      constructor
      constructor
      { easy }
      { apply Typed.sub
        { apply Typed.copen hct }
        { apply Subcapt.refl }
        { subst he1
          exact hs1 } }
      { have h1 := Typed.capp_inv_capt ht
        have h2 := WellScoped.subcapt hsc h1
        simp [CaptureSet.cweaken, CaptureSet.copen, CaptureSet.crename_crename]
        simp [FinFun.open_comp_weaken, CaptureSet.crename_id]
        apply WellScoped.var_inv
        exact h2
        easy }
      easy
  case unbox hl =>
    cases ht
    case mk hs hsc ht hc =>
      have hg := TypedStore.is_tight hs
      have ⟨S0, hx, he0⟩ := Typed.unbox_inv ht
      have ⟨Sv, Cv, Cv0, hv, hbx, hvs⟩ := Store.lookup_inv_typing hl hs hx
      have hv' := value_typing_widen hv hvs
      have hct := Typed.canonical_form_boxed hg hv'
      constructor
      constructor
      { easy }
      { apply Typed.sub
        exact hct
        apply Subcapt.refl
        apply he0 }
      { have h1 := Typed.unbox_inv_capt ht
        have h2 := WellScoped.subcapt hsc h1
        have h3 := Typing.inv_subcapt hct
        have h4 := WellScoped.subcapt h2 h3
        easy }
      { easy }
  case push =>
    cases ht
    case mk hs hsc ht hc =>
      have ⟨T, E0, htt, htu, hsub⟩ := Typed.letin_inv ht
      constructor
      constructor
      { easy }
      { exact htt }
      { apply WellScoped.cons; easy }
      { constructor
        apply Typed.sub <;> try easy
        apply Subcapt.refl
        apply ESubtyp.weaken; easy
        { easy }
        easy }
  case push_ex =>
    cases ht
    case mk hs hsc ht hc =>
      have ⟨T, E0, htt, htu, hsub⟩ := Typed.letex_inv ht
      constructor
      constructor
      { exact hs }
      { exact htt }
      { apply WellScoped.conse; easy }
      { constructor
        apply Typed.sub; exact htu; apply Subcapt.refl
        apply ESubtyp.weaken
        apply ESubtyp.cweaken; exact hsub
        { easy }
        exact hc }
  case rename =>
    cases ht
    case mk hs hsc hx hc =>
      cases hc
      case cons hu hsc0 hc0 =>
        have hu1 := hu.open hx
        simp [EType.weaken, EType.open] at hu1
        simp [EType.rename_rename] at hu1
        simp [FinFun.open_comp_weaken] at hu1
        simp [EType.rename_id] at hu1
        constructor
        constructor <;> try easy
        simp [CaptureSet.weaken, CaptureSet.open]
        simp [CaptureSet.rename_rename]
        simp [FinFun.open_comp_weaken, CaptureSet.rename_id]
        easy
  case lift_ex =>
    cases ht
    case mk hs hsc ht hc =>
      cases hc
      case conse hu hsc hc0 =>
        have hg := TypedStore.is_tight hs
        have hx := Typed.canonical_form_pack hg ht
        rename_i C _ _ _ _ _ _ _
        have hu1 := hu.cinstantiate_extvar (C := C)
        have hu2 := hu1.open hx
        simp [EType.weaken, EType.open, EType.rename_rename] at hu2
        simp [FinFun.open_comp_weaken] at hu2
        simp [EType.rename_id] at hu2
        apply Preserve.mk_cweaken
        constructor
        { constructor; exact hs }
        { exact hu2 }
        { simp [CaptureSet.weaken, CaptureSet.open]
          simp [CaptureSet.rename_rename, FinFun.open_comp_weaken]
          simp [CaptureSet.rename_id]
          apply hsc.cweaken }
        { apply TypedCont.cweaken; exact hc0 }
  case lift hv =>
    cases ht
    case mk hs hsc ht hc =>
      cases hc
      case cons hu hsc0 hc0 =>
        apply Preserve.mk_weaken
        constructor
        { constructor; exact hs; exact ht }
        { exact hu }
        { apply hsc0.weaken }
        { apply TypedCont.weaken; exact hc0 }
  case tlift =>
    cases ht
    case mk hs hsc ht hc =>
      apply Preserve.mk_tweaken
      have ⟨E0, ht, hsub⟩ := Typed.bindt_inv ht
      constructor
      { constructor; exact hs }
      { apply Typed.sub
        exact ht; apply Subcapt.refl
        apply ESubtyp.tweaken; exact hsub }
      { apply hsc.tweaken }
      { apply TypedCont.tweaken; exact hc }
  case clift =>
    cases ht
    case mk hs hsc ht hc =>
      apply Preserve.mk_cweaken
      have ⟨E0, ht, hsub⟩ := Typed.bindc_inv ht
      constructor
      { constructor; exact hs }
      { apply Typed.sub
        exact ht; apply Subcapt.refl
        apply ESubtyp.cweaken; exact hsub }
      { apply hsc.cweaken }
      { apply TypedCont.cweaken; exact hc }
  case enter => sorry
  case leave_var => sorry
  case leave_val => sorry
  case invoke => sorry

end Capless
