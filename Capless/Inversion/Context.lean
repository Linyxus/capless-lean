import Capless.Context
import Capless.Store
namespace Capless

theorem Context.var_bound_succ_inv'
  (he1 : Γ0 = Γ.var P) (he1 : x0 = x.succ)
  (hb : Context.Bound Γ0 x0 T) :
  ∃ T0, Context.Bound Γ x T0 ∧ T = T0.weaken := by
  cases hb <;> try (solve | cases he1 | cases he2)
  rw [Fin.succ_inj] at he1
  subst he1
  cases he1
  rename_i T0 hb
  exists T0

theorem Context.var_bound_succ_inv
  (hb : Context.Bound (Γ.var P) x.succ T) :
  ∃ T0, Context.Bound Γ x T0 ∧ T = T0.weaken :=
  Context.var_bound_succ_inv' rfl rfl hb

theorem Context.var_tbound_inv'
  (he : Γ0 = Γ.var P)
  (hb : Context.TBound Γ0 X b) :
  ∃ b0, Context.TBound Γ X b0 ∧ b = b0.weaken := by
  cases hb <;> try (solve | cases he)
  case there_var b0 _ hb0 => cases he; exists b0

theorem Context.var_tbound_inv
  (hb : Context.TBound (Γ.var P) X b) :
  ∃ b0, Context.TBound Γ X b0 ∧ b = b0.weaken :=
  Context.var_tbound_inv' rfl hb

theorem Context.var_tbound_inv_bound
  (hb : Context.TBound (Γ.var P) X (TBinding.bound S)) :
  ∃ S0, Context.TBound Γ X (TBinding.bound S0) ∧ S = SType.weaken S0 := by
  have h := Context.var_tbound_inv hb
  have ⟨b0, hb0, he0⟩ := h
  cases b0
  case bound S0 =>
    simp [TBinding.weaken, TBinding.rename] at he0
    simp [SType.weaken]
    exists S0
  case inst => simp [TBinding.weaken, TBinding.rename] at he0

theorem Context.tinst_tbound_bound_inv'
  (he1 : Γ0 = Γ.tvar (TBinding.inst P))
  (he2 : b0 = TBinding.bound S)
  (hb : Context.TBound Γ0 X b0) :
  ∃ X0 S0, Context.TBound Γ X0 (TBinding.bound S0)
    ∧ S = SType.tweaken S0
    ∧ X = X0.succ := by
  cases hb <;> try (solve | cases he1 | cases he2)
  case here =>
    cases he1
    simp [TBinding.tweaken, TBinding.rename] at he2
    cases he2
  case there_tvar hb0 =>
    cases he1
    rename_i X0 b0
    cases b0 <;> simp [TBinding.tweaken, TBinding.trename] at he2
    rename_i S0
    apply Exists.intro X0
    apply Exists.intro S0
    constructor <;> try constructor
    { trivial }
    { simp [SType.tweaken]; aesop }
    { trivial }

theorem Context.tinst_tbound_bound_inv
  (hb : Context.TBound (Γ.tvar (TBinding.inst P)) X (TBinding.bound S)) :
  ∃ X0 S0, Context.TBound Γ X0 (TBinding.bound S0)
    ∧ S = SType.tweaken S0
    ∧ X = X0.succ :=
  Context.tinst_tbound_bound_inv' rfl rfl hb

theorem Context.cvar_tbound_inv
  (hb : Context.TBound (Γ.cvar p) X b) :
  ∃ b0, Context.TBound Γ X b0 ∧ b = b0.cweaken := sorry

theorem Context.tight_bound_tvar_absurd
  (ht : Context.IsTight Γ)
  (hb : Context.TBound Γ X (TBinding.bound S)) : False := by
  induction ht
  case empty => cases hb
  case var ih =>
    have ⟨S0, hb0, he0⟩ := Context.var_tbound_inv_bound hb
    aesop
  case tvar =>
    have ⟨X0, S0, hb0, hs0, hx0⟩ := Context.tinst_tbound_bound_inv hb
    aesop
  case cvar => sorry

end Capless
