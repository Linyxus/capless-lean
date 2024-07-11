import Capless.Context
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

end Capless
