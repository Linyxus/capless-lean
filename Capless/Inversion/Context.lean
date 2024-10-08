import Capless.Context
import Capless.Store
namespace Capless

theorem Context.var_bound_succ_inv'
  (he1 : Γ0 = Γ.var P) (he1 : x0 = x.succ)
  (hb : Context.Bound Γ0 x0 T) :
  ∃ T0, Context.Bound Γ x T0 ∧ T = T0.weaken := by
  cases hb <;> try (solve | cases he1 | cases he2 | aesop)

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

theorem Context.var_cbound_inv'
  (he : Γ0 = Γ.var P)
  (hb : Context.CBound Γ0 X b) :
  ∃ b0, Context.CBound Γ X b0 ∧ b = b0.weaken := by
  cases hb <;> try (solve | cases he)
  case there_var b0 _ _ hb0 =>  cases he; exists b0

theorem Context.var_cbound_inv
  (hb : Context.CBound (Γ.var P) X b) :
  ∃ b0, Context.CBound Γ X b0 ∧ b = b0.weaken :=
  Context.var_cbound_inv' rfl hb

theorem Context.var_cbound_inv_bound
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

theorem Context.label_tbound_inv'
  (he : Γ0 = Γ.label l)
  (hb : Context.TBound Γ0 X b) :
  ∃ b0, Context.TBound Γ X b0 ∧ b = b0.weaken := by
  cases hb <;> try (solve | cases he)
  case there_label b0 hb0 => aesop

theorem Context.label_tbound_inv
  (hb : Context.TBound (Γ.label l) X b) :
  ∃ b0, Context.TBound Γ X b0 ∧ b = b0.weaken :=
  Context.label_tbound_inv' rfl hb

theorem Context.label_tbound_inv_bound
  (hb : Context.TBound (Γ.label l) X (TBinding.bound S)) :
  ∃ S0, Context.TBound Γ X (TBinding.bound S0) ∧ S = SType.weaken S0 := by
  have ⟨b0, hb0, he0⟩ := Context.label_tbound_inv hb
  cases b0
  case bound S0 =>
    simp [TBinding.weaken, TBinding.rename] at he0
    aesop
  case inst => simp [TBinding.weaken, TBinding.rename] at he0

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
  case label =>
    have ⟨S0, hb0, he0⟩ := Context.label_tbound_inv_bound hb
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

theorem Context.cvar_tbound_tvar_inv'
  (he : Γ0 = Context.cvar Γ b)
  (hb : Context.TBound Γ0 X T) :
  ∃ T0, Context.TBound Γ X T0 ∧ T = T0.cweaken := by
  cases hb <;> try (solve | cases he)
  case there_cvar =>
    cases he
    rename_i E0 _
    exists E0

theorem Context.cvar_tbound_tvar_inv
  (hb : Context.TBound (Context.cvar Γ b) X T) :
  ∃ T0, Context.TBound Γ X T0 ∧ T = T0.cweaken :=
  Context.cvar_tbound_tvar_inv' rfl hb

theorem Context.tvar_tbound_inv'
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

theorem Context.tvar_tbound_inv
  (hb : Context.TBound (Γ.tvar p) X b) :
  (X = 0 ∧ b = p.tweaken) ∨
  (∃ b0 X0, Context.TBound Γ X0 b0 ∧ b = b0.tweaken ∧ X = (Fin.succ X0)) :=
  Context.tvar_tbound_inv' rfl hb

theorem Context.cvar_cbound_succ_inv'
  (he1 : Γ0 = Γ.cvar p) (he2 : X0 = Fin.succ X)
  (hb : Context.CBound Γ0 X0 b) :
  ∃ b0, Context.CBound Γ X b0 ∧ b = b0.cweaken := by
  cases hb <;> try (solve | cases he1 | cases he2)
  case there_cvar hb0 =>
    rw [Fin.succ_inj] at he2
    cases he1; subst he2
    aesop

theorem Context.cvar_cbound_succ_inv
  (hb : Context.CBound (Γ.cvar p) (Fin.succ X) b) :
  ∃ b0, Context.CBound Γ X b0 ∧ b = b0.cweaken :=
  Context.cvar_cbound_succ_inv' rfl rfl hb

theorem Context.cvar_cbound_inv'
  (he1 : Γ0 = Γ.cvar p)
  (hb : Context.CBound Γ0 X0 b) :
  (X0 = 0 ∧ b = p.cweaken) ∨
  (∃ b0 X, Context.CBound Γ X b0 ∧ b = b0.cweaken ∧ X0 = (Fin.succ X)) := by
  cases X0 using Fin.cases
  case zero =>
    left
    cases hb <;> try (solve | cases he1 | cases he2 | aesop)
  case succ n =>
    right
    rw [he1] at hb
    apply Context.cvar_cbound_succ_inv at hb
    aesop

theorem Context.cvar_cbound_inv
  (hb : Context.CBound (Γ.cvar p) X b) :
  (X = 0 ∧ b = p.cweaken) ∨
  (∃ b0 X0, Context.CBound Γ X0 b0 ∧ b = b0.cweaken ∧ X = (Fin.succ X0)) :=
  Context.cvar_cbound_inv' rfl hb

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
  case label Γ0 l ih =>
    cases h1
    cases h2
    rename_i h1 _ h2
    have ih := ih h1 h2
    aesop

theorem Context.var_lbound_succ_inv'
  (he1 : Γ0 = Γ.var T) (he2 : x0 = x.succ)
  (hb : Context.LBound Γ0 x0 S) :
  ∃ S0, Context.LBound Γ x S0 ∧ S = S0.weaken := by
  cases hb <;> try (solve | cases he1 | cases he2)
  case there_var => aesop

theorem Context.var_lbound_succ_inv
  (hb : Context.LBound (Γ.var T) x.succ S) :
  ∃ S0, Context.LBound Γ x S0 ∧ S = S0.weaken := by
  apply Context.var_lbound_succ_inv' rfl rfl hb

theorem Context.label_lbound_succ_inv'
  (he1 : Γ0 = Γ.label l) (he2 : x0 = x.succ)
  (hb : Context.LBound Γ0 x0 S) :
  ∃ S0, Context.LBound Γ x S0 ∧ S = S0.weaken := by
  cases hb <;> try (solve | cases he1 | cases he2)
  case there_label => aesop

theorem Context.label_lbound_succ_inv
  (hb : Context.LBound (Γ.label l) x.succ S) :
  ∃ S0, Context.LBound Γ x S0 ∧ S = S0.weaken := by
  apply Context.label_lbound_succ_inv' rfl rfl hb

theorem Context.bound_lbound_absurd
  (hb1 : Context.Bound Γ x T)
  (hb2 : Context.LBound Γ x S) : False := by
  induction Γ
  case empty => cases hb1
  case var ih =>
    cases hb1
    case here =>
      cases hb2
    case there_var =>
      have ⟨_, _, _⟩ := Context.var_lbound_succ_inv hb2
      apply! ih
  case tvar ih =>
    cases hb1; cases hb2
    apply ih <;> assumption
  case cvar ih =>
    cases hb1; cases hb2
    apply ih <;> assumption
  case label ih =>
    cases hb1
    case there_label =>
      have ⟨_, _, _⟩ := Context.label_lbound_succ_inv hb2
      apply ih <;> assumption

theorem Context.label_bound_succ_inv'
  (he1 : Γ0 = Γ.label l) (he2 : x0 = x.succ)
  (hb : Context.Bound Γ0 x0 T) :
  ∃ T0, Context.Bound Γ x T0 ∧ T = T0.weaken := by
  cases hb <;> try (solve | cases he1 | cases he2)
  case there_label => aesop

theorem Context.label_bound_succ_inv
  (hb : Context.Bound (Γ.label l) x.succ T) :
  ∃ T0, Context.Bound Γ x T0 ∧ T = T0.weaken := by
  apply Context.label_bound_succ_inv' rfl rfl hb

theorem Context.cbound_injective
  (hb1 : Context.CBound Γ c b1)
  (hb2 : Context.CBound Γ c b2) : b1 = b2 := by
  induction hb1
  case here => cases hb2; rfl
  case there_var ih =>
    cases hb2
    rename_i hb2
    have ih := ih hb2
    aesop
  case there_tvar ih =>
    cases hb2
    rename_i hb2
    have ih := ih hb2
    aesop
  case there_cvar ih =>
    have ⟨b2, hb2, he2⟩ := Context.cvar_cbound_succ_inv hb2
    have ih := ih hb2
    aesop
  case there_label ih =>
    cases hb2
    rename_i hb2
    have ih := ih hb2
    aesop

theorem Context.bound_injective
  (hb1 : Context.Bound Γ x T1)
  (hb2 : Context.Bound Γ x T2) : T1 = T2 := by
  induction hb2
  case here =>
    cases hb1
    rfl
  case there_var ih =>
    have ⟨T1, hb1, he1⟩ := Context.var_bound_succ_inv hb1
    aesop
  case there_tvar =>
    cases hb1
    aesop
  case there_cvar =>
    cases hb1
    aesop
  case there_label ih =>
    have ⟨T1, hb1, he1⟩ := Context.label_bound_succ_inv hb1
    aesop

theorem Context.lbound_inj
  (hb1 : Context.LBound Γ x S1)
  (hb2 : Context.LBound Γ x S2) : S1 = S2 := by
  induction hb1
  case here => cases hb2; rfl
  case there_var ih =>
    have ⟨S2, hb2, he2⟩ := Context.var_lbound_succ_inv hb2
    have ih := ih hb2
    aesop
  case there_tvar ih =>
    cases hb2; rename_i hb2
    have ih := ih hb2
    aesop
  case there_cvar ih =>
    cases hb2; rename_i hb2
    have ih := ih hb2
    aesop
  case there_label ih =>
    have ⟨S2, hb2, he2⟩ := Context.label_lbound_succ_inv hb2
    have ih := ih hb2
    aesop

theorem Context.var_cbound_inv_inst'
  (he : b = CBinding.inst C)
  (hb : Context.CBound (Γ.var T) c b) :
  ∃ C0, Context.CBound Γ c (CBinding.inst C0) ∧ C = C0.weaken := by
  cases hb
  case there_var b0 hb =>
    cases b0 <;> cases he
    aesop

theorem Context.var_cbound_inv_inst
  (hb : Context.CBound (Γ.var T) c (CBinding.inst C)) :
  ∃ C0, Context.CBound Γ c (CBinding.inst C0) ∧ C = C0.weaken := by
  apply Context.var_cbound_inv_inst' rfl hb

theorem Context.cvar_bound_cbound_inv_inst'
  (he : b = CBinding.inst C)
  (hb : Context.CBound (Γ,c:CapSet) c b) :
  ∃ c0 C0, Context.CBound Γ c0 (CBinding.inst C0)
    ∧ c = c0.succ
    ∧ C = C0.cweaken := by
  cases hb
  case here => cases he
  case there_cvar b hb =>
    cases b; cases he
    cases he
    aesop

theorem Context.cvar_bound_cbound_inv_inst
  (hb : Context.CBound (Γ,c:CapSet) c (CBinding.inst C)) :
  ∃ c0 C0, Context.CBound Γ c0 (CBinding.inst C0)
    ∧ c = c0.succ
    ∧ C = C0.cweaken := by
  apply Context.cvar_bound_cbound_inv_inst' rfl hb

end Capless
