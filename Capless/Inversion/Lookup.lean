import Capless.Store
import Capless.Renaming.Term.Typing
import Capless.Renaming.Type.Typing
import Capless.Renaming.Capture.Typing
import Capless.Inversion.Context
import Capless.Inversion.Typing
namespace Capless

def Store.lookup_inv_bound
  (hl : Store.Bound σ x v)
  (ht : TypedStore σ Γ)
  (hb : Context.Bound Γ x T) :
  ∃ Cv, Typed Γ v (EType.type T) Cv := by
  induction ht
  case empty => cases hb
  case val ih =>
    cases hl
    case here =>
      cases hb
      rename_i E _ _ ht _ _
      have ht1 := ht.weaken (T := E)
      simp [EType.weaken, EType.rename, CType.weaken] at *
      constructor; exact ht1
    case there_val  =>
      have ⟨T1, hb1, heq⟩ := Context.var_bound_succ_inv hb
      subst heq
      rename_i hl _
      have ⟨Cv0, ih⟩ := ih hl hb1
      rename_i E _ _ _ _ _ _ _ _
      have ih := ih.weaken (T := E)
      simp [EType.weaken, EType.rename, CType.weaken] at *
      constructor; exact ih
  case tval S _ ih =>
    cases hb; cases hl
    rename_i hb _ hl
    have ⟨Cv0, ih⟩ := ih hl hb
    have ih := ih.tweaken (b := TBinding.inst S)
    simp [EType.tweaken, EType.trename, CType.tweaken] at *
    constructor; exact ih
  case cval C _ ih =>
    cases hb; cases hl
    rename_i hb _ hl
    have ⟨Cv0, ih⟩ := ih hl hb
    have ih := ih.cweaken (b := CBinding.inst C)
    simp [EType.cweaken, EType.crename, CType.cweaken] at *
    constructor; exact ih
  case label S _ ih =>
    cases hl
    have ⟨T1, hb1, heq⟩ := Context.label_bound_succ_inv hb
    subst heq
    rename_i hl
    have ⟨Cv0, ih⟩ := ih hl hb1
    have ih := ih.lweaken (S := S)
    aesop

theorem Store.bound_type
  (hl : Store.Bound σ x v)
  (ht : TypedStore σ Γ) :
  ∃ T0, Context.Bound Γ x T0 := by
  induction ht
  case empty => cases hl
  case val ih =>
    cases hl
    case here => constructor; constructor
    case there_val hb0 _ =>
      have ⟨_, ih⟩ := ih hb0
      apply Exists.intro
      apply Context.Bound.there_var
      exact ih
  case tval ih =>
    cases hl
    case there_tval hb0 =>
      have ⟨_, ih⟩ := ih hb0
      apply Exists.intro
      apply Context.Bound.there_tvar
      exact ih
  case cval ih =>
    cases hl
    case there_cval hb0 =>
      have ⟨_, ih⟩ := ih hb0
      apply Exists.intro
      apply Context.Bound.there_cvar
      exact ih
  case label ih =>
    cases hl
    case there_label hb0 =>
      have ⟨_, ih⟩ := ih hb0
      apply Exists.intro
      apply Context.Bound.there_label
      exact ih

theorem Store.lookup_inv_typing
  (hl : Store.Bound σ x v)
  (ht : TypedStore σ Γ)
  (hx : Typed Γ (Term.var x) (EType.type (S^C)) Cx) :
  ∃ S0 C0 Cv0,
    Typed Γ v (EType.type (S0^C0)) Cv0 ∧
    Γ.Bound x (S0^C0) ∧
    (Γ ⊢ (S0^{x=x}) <: (S^C)) := by
  have ⟨Tx, hbx⟩ := Store.bound_type hl ht
  have ⟨C0, S0, hb, hsub⟩ := Typed.var_inv hx hbx
  have ⟨Cv0, hv⟩ := Store.lookup_inv_bound hl ht hb
  repeat apply Exists.intro
  repeat any_goals apply And.intro
  all_goals easy

theorem Store.lookup_inv_typing_alt
  (hl : Store.Bound σ x v)
  (ht : TypedStore σ Γ)
  (hx : Typed Γ (Term.var x) (EType.type (S^C)) Cx) :
  ∃ C0 Cv0, Typed Γ v (EType.type (S^C0)) Cv0 := by
  have ⟨Sv, Cv, Cv0, htv, _, hsv⟩ := Store.lookup_inv_typing hl ht hx
  cases hsv; rename_i hsv
  repeat apply Exists.intro
  apply Typed.sub
  { exact htv }
  { apply Subcapt.refl }
  { constructor; constructor; apply Subcapt.refl; easy }

theorem Store.bound_label
  (hl : Store.LBound σ x S)
  (ht : TypedStore σ Γ) :
  Γ.LBound x S := by
  induction ht <;> cases hl <;> try (solve | constructor; aesop)
  case label ih => constructor

theorem Cont.has_label_tail_inv
  (htc : TypedCont Γ E1 cont E2 Ct)
  (hb : Γ.LBound x S0)
  (hh : cont.HasLabel x tail) :
  ∃ Ct1, TypedCont Γ (S0^{}) tail E2 Ct1 := by
  induction hh generalizing E1 E2 Ct <;> try (solve | cases htc; aesop)
  case here =>
    cases htc; rename_i hb0 htc0
    have he := Context.lbound_inj hb hb0
    cases he
    aesop

end Capless
