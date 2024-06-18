import Capless.Basic
import Capless.Context
import Capless.CaptureSet
import Capless.Typing
namespace Capless

structure VarSubst (Γ : Context n m k) (f : FinFun n n') (Δ : Context n' m k) where
  map : ∀ x E, Γ.Bound x E -> Typed Δ (Term.var (f x)) (E.rename f)
  tmap : ∀ X b, Γ.TBound X b -> Δ.TBound X (b.rename f)
  cmap : ∀ c b, Γ.CBound c b -> Δ.CBound c (b.rename f)

end Capless
