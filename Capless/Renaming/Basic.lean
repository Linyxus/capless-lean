import Capless.Basic
import Capless.Context
namespace Capless

-- def VarRename (Γ : Context n m k) (f : FinFun n n') (Δ : Context n' m k) : Prop :=
--   ∀ x E, Γ.Bound x E -> Δ.Bound (f x) (E.rename f)

structure VarMap (Γ : Context n m k) (f : FinFun n n') (Δ : Context n' m k) where
  map : ∀ x E, Γ.Bound x E -> Δ.Bound (f x) (E.rename f)
  tmap : ∀ X b, Γ.TBound X b -> Δ.TBound X (b.rename f)
  cmap : ∀ c b, Γ.CBound c b -> Δ.CBound c (b.rename f)

end Capless
