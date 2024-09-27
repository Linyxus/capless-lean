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
      have ⟨Cv, Cv0, hv⟩ := Store.lookup_inv_typing hl hs hx
      have ⟨hcfs, C0, hcft⟩ := Typed.canonical_form_lam hg hv
      constructor
      constructor
      { assumption }
      { apply Typed.sub
        { apply Typed.open (h := hcft)
          exact hy }
        { apply Subcapt.refl }
        { subst he1
          assumption } }
      { sorry }
      { assumption }
  case tapply hl =>
    cases ht
    case mk hs hsc ht hc =>
      have hg := TypedStore.is_tight hs
      have ⟨Cf, F, E0, hx, he0, hs0⟩ := Typed.tapp_inv ht
      have ⟨Cv, Cv0, hv⟩ := Store.lookup_inv_typing hl hs hx
      have ⟨hs1, C0, hft⟩ := Typed.canonical_form_tlam hg hv
      constructor
      constructor
      { easy }
      { apply Typed.sub
        { apply Typed.topen (h := hft) }
        { apply Subcapt.refl }
        { subst he0
          easy } }
      { sorry }
      easy
  case capply hl =>
    cases ht
    case mk hs hsc ht hc =>
      have hg := TypedStore.is_tight hs
      have ⟨Cf, F, E0, hx, he1, hs1⟩ := Typed.capp_inv ht
      have ⟨Cv, Cv0, hv⟩ := Store.lookup_inv_typing hl hs hx
      have ⟨C0, hct⟩ := Typed.canonical_form_clam hg hv
      constructor
      constructor
      { easy }
      { apply Typed.sub
        { apply Typed.copen hct }
        { apply Subcapt.refl }
        { subst he1
          exact hs1 } }
      { sorry }
      easy
  case unbox hl =>
    cases ht
    case mk hs hsc ht hc =>
      have hg := TypedStore.is_tight hs
      have ⟨S0, hx, he0⟩ := Typed.unbox_inv ht
      have ⟨Cv, Cv0, hv⟩ := Store.lookup_inv_typing hl hs hx
      have hct := Typed.canonical_form_boxed hg hv
      constructor
      constructor
      { trivial }
      { apply Typed.sub
        exact hct
        apply Subcapt.refl
        apply he0 }
      { sorry }
      { easy }
  case push =>
    cases ht
    case mk hs hsc ht hc =>
      have ⟨T, E0, C0, htt, htu, hsub⟩ := Typed.letin_inv ht
      constructor
      constructor
      { easy }
      { exact htt }
      { sorry }
      { constructor
        apply? Typed.sub
        apply Subcapt.refl
        apply! ESubtyp.weaken
        { sorry }
        easy }
  case push_ex =>
    cases ht
    case mk hs hsc ht hc =>
      have ⟨T, E0, C0, htt, htu, hsub⟩ := Typed.letex_inv ht
      constructor
      constructor
      { exact hs }
      { exact htt }
      { sorry }
      { constructor
        apply Typed.sub; exact htu; apply Subcapt.refl
        apply ESubtyp.weaken
        apply ESubtyp.cweaken; exact hsub
        { sorry }
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
        apply TypedState.mk hs hu1 sorry hc0
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
        { sorry }
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
        { sorry }
        { apply TypedCont.weaken; exact hc0 }
  case tlift =>
    cases ht
    case mk hs hsc ht hc =>
      apply Preserve.mk_tweaken
      have ⟨E0, C0, ht, hsub⟩ := Typed.bindt_inv ht
      constructor
      { constructor; exact hs }
      { apply Typed.sub
        exact ht; apply Subcapt.refl
        apply ESubtyp.tweaken; exact hsub }
      { sorry }
      { apply TypedCont.tweaken; exact hc }
  case clift =>
    cases ht
    case mk hs hsc ht hc =>
      apply Preserve.mk_cweaken
      have ⟨E0, C0, ht, hsub⟩ := Typed.bindc_inv ht
      constructor
      { constructor; exact hs }
      { apply Typed.sub
        exact ht; apply Subcapt.refl
        apply ESubtyp.cweaken; exact hsub }
      { sorry }
      { apply TypedCont.cweaken; exact hc }
  case enter => sorry
  case leave_var => sorry
  case leave_val => sorry
  case invoke => sorry

end Capless
