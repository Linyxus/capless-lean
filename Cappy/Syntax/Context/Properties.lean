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

end Cappy
