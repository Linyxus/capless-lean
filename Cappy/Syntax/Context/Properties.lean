import Cappy.Syntax.Context.Core
namespace Cappy

theorem Context.var_bound_succ'
  (he1 : Γ0 = Γ.var P) (he2 : x0 = x.succ)
  (hb : Context.Bound Γ0 x0 T) :
  ∃ T0, Context.Bound Γ x T0 ∧ T = T0.weaken := by
  cases hb <;> try (solve | cases he1 | cases he2)
  cases he1
  rw [Fin.succ_inj] at he2
  aesop

theorem Context.var_bound_succ
  (hb : Context.Bound (Context.var Γ P) x.succ T) :
  ∃ T0, Context.Bound Γ x T0 ∧ T = T0.weaken :=
  Context.var_bound_succ' rfl rfl hb

theorem Context.bound_inj
  (hb1 : Context.Bound Γ x T1)
  (hb2 : Context.Bound Γ x T2) :
  T1 = T2 := by
  induction hb1
  case here => cases hb2; rfl
  case there_var ih =>
    have ⟨T0, hb2, heq⟩ := Context.var_bound_succ hb2
    have ih := ih hb2
    aesop
  case there_tvar ih =>
    cases hb2; rename_i hb2
    have ih := ih hb2
    aesop

theorem Context.bound_exists {x : Fin n} {Γ : Context n m} :
  ∃ T, Context.Bound Γ x T := by
  induction Γ
  case empty => apply Fin.elim0 x
  case var ih =>
    cases x using Fin.cases
    case zero => constructor; constructor
    case succ x0 =>
      have ⟨T0, ih⟩ := ih (x := x0)
      constructor; constructor
      assumption
  case tvar ih =>
    have ⟨T0, ih⟩ := ih (x := x)
    constructor; constructor
    assumption

theorem Context.var_bound_succ_exists {x : Fin (n+1)} {Γ : Context (n+1) m} :
  ∃ T, Context.Bound Γ x (CType.weaken T) := by
  cases Γ
  case var Γ0 P0 =>
    cases x using Fin.cases
    case zero => constructor; constructor
    case succ x0 =>
      have ⟨T0, h0⟩ := Context.bound_exists (Γ := Γ0) (x := x0)
      constructor; constructor
      assumption
  case tvar Γ0 R0 => sorry

end Cappy
