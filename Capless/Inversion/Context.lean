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

theorem Context.tbound_tbound_inst_inv'
  (he1 : Γ0 = Γ.tvar (TBinding.bound P))
  (he2 : b0 = TBinding.inst S)
  (hb : Context.TBound Γ0 X b0) :
  ∃ X0 S0, Context.TBound Γ X0 (TBinding.inst S0)
    ∧ S = SType.tweaken S0
    ∧ X = X0.succ := by
  cases hb <;> try (solve | cases he1 | cases he2)
  case here =>
    cases he1
    simp [TBinding.tweaken, TBinding.trename] at he2
  case there_tvar hb0 =>
    cases he1
    rename_i X0 b0
    cases b0 <;> simp [TBinding.tweaken, TBinding.trename] at he2
    case inst S0 =>
      apply Exists.intro X0
      apply Exists.intro S0
      constructor <;> try constructor
      { trivial }
      { simp [SType.tweaken]; aesop }
      { trivial }

theorem Context.tbound_tbound_inst_inv
  (hb : Context.TBound (Γ.tvar (TBinding.bound P)) X (TBinding.inst S)) :
  ∃ X0 S0, Context.TBound Γ X0 (TBinding.inst S0)
    ∧ S = SType.tweaken S0
    ∧ X = X0.succ :=
  Context.tbound_tbound_inst_inv' rfl rfl hb

theorem Context.cvar_tbound_inv'
  (he : Γ0 = Γ.cvar p)
  (hb : Context.TBound Γ0 X b) :
  ∃ b0, Context.TBound Γ X b0 ∧ b = b0.cweaken := by
  cases hb <;> try (solve | cases he)
  case there_cvar b0 hb0 =>
    cases he
    exists b0

theorem Context.cvar_tbound_inv
  (hb : Context.TBound (Γ.cvar p) X b) :
  ∃ b0, Context.TBound Γ X b0 ∧ b = b0.cweaken :=
  Context.cvar_tbound_inv' rfl hb

theorem Context.cvar_tbound_inv_bound
  (hb : Context.TBound (Γ.cvar p) X (TBinding.bound S)) :
  ∃ S0, Context.TBound Γ X (TBinding.bound S0) ∧ S = S0.cweaken := by
  have ⟨b0, hb0, he0⟩ := Context.cvar_tbound_inv hb
  cases b0
  case bound S0 =>
    simp [TBinding.cweaken, TBinding.crename] at he0
    apply Exists.intro S0
    aesop
  case inst =>
    simp [TBinding.cweaken, TBinding.crename] at he0

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
  case cvar =>
    have ⟨S0, hb0, he0⟩ := Context.cvar_tbound_inv_bound hb
    aesop

theorem Context.tvar_tbound_succ_inv'
  (he1 : Γ0 = Γ.tvar p) (he2 : X0 = Fin.succ X)
  (hb : Context.TBound Γ0 X0 b) :
  ∃ b0, Context.TBound Γ X b0 ∧ b = b0.tweaken := by
  cases hb <;> try (solve | cases he1 | cases he2)
  case there_tvar hb0 =>
    rw [Fin.succ_inj] at he2
    cases he1; subst he2
    aesop

theorem Context.tvar_tbound_succ_inv
  (hb : Context.TBound (Γ.tvar p) (Fin.succ X) b) :
  ∃ b0, Context.TBound Γ X b0 ∧ b = b0.tweaken :=
  Context.tvar_tbound_succ_inv' rfl rfl hb

theorem Context.tbound_inj
  (h1 : Context.TBound Γ X b1)
  (h2 : Context.TBound Γ X b2) : b1 = b2 := by
  induction Γ
  case empty => cases h1
  case var Γ0 P ih =>
    cases h1
    cases h2
    rename_i h1 _ h2
    have ih := ih h1 h2
    aesop
  case tvar Γ0 b ih =>
    cases h1
    case here =>
      cases h2
      trivial
    case there_tvar h1 =>
      have h := Context.tvar_tbound_succ_inv h2
      have ⟨b0, h2, he2⟩ := h
      have ih := ih h1 h2
      aesop
  case cvar Γ0 b ih =>
    cases h1
    cases h2
    rename_i h1 _ h2
    have ih := ih h1 h2
    aesop

end Capless
