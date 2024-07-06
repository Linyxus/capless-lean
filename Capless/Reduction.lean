import Capless.Term
import Capless.Store
namespace Capless

-- structure Config (n m k : Nat) where
--   σ : Store n m k
--   t : Term n m k

-- inductive Reduce : Config n m k -> Config n' m' k' -> Prop where
-- | ctx :
--   Reduce ⟨σ1, t1⟩ ⟨σ2, t2⟩ ->
--   Reduce ⟨σ1, Term.letin t1 u⟩ ⟨σ2, Term.letin t2 u⟩
-- | apply {σ : Store n m k} :
--   σ.Bound x (Term.lam T t) ->
--   Reduce ⟨σ, Term.app x y⟩ ⟨σ, t.open x⟩
-- | tapply {σ : Store n m k} :
--   σ.Bound x (Term.tlam S t) ->
--   Reduce ⟨σ, Term.tapp x X⟩ ⟨σ, t.topen X⟩
-- | capply {σ : Store n m k} :
--   σ.Bound x (Term.clam t) ->
--   Reduce ⟨σ, Term.capp x c⟩ ⟨σ, t.copen c⟩
-- | unbox {σ : Store n m k} :
--   σ.Bound x (Term.boxed y) ->
--   Reduce ⟨σ, Term.unbox C x⟩ ⟨σ, Term.var y⟩
-- | rename :
--   Reduce ⟨σ, Term.letin (Term.var x) t⟩ ⟨σ, t.open x⟩
-- | lift :
--   (hv : Term.IsValue t) ->
--   Reduce ⟨σ, Term.letin t u⟩ ⟨σ.val t hv, u⟩
-- | tlift :
--   Reduce ⟨σ, Term.bindt S t⟩ ⟨σ.tval S, t⟩
-- | clift :
--   Reduce ⟨σ, Term.bindc C t⟩ ⟨σ.cval C, t⟩

inductive Reduce : State n m k -> State n m k' -> Prop where
| apply {σ : Store n m k} :
  σ.Bound x (Term.lam T t) ->
  Reduce ⟨σ, cont, Term.app x y⟩ ⟨σ, cont, t.open x⟩
| tapply {σ : Store n m k} :
  σ.Bound x (Term.tlam S t) ->
  Reduce ⟨σ, cont, Term.tapp x X⟩ ⟨σ, cont, t.topen X⟩
| capply {σ : Store n m k} :
  σ.Bound x (Term.clam t) ->
  Reduce ⟨σ, cont, Term.capp x c⟩ ⟨σ, cont, t.copen c⟩
| unbox {σ : Store n m k} :
  σ.Bound x (Term.boxed y) ->
  Reduce ⟨σ, cont, Term.unbox C x⟩ ⟨σ, cont, Term.var y⟩
| push :
  Reduce
    ⟨σ, cont, Term.letin t u⟩
    ⟨σ, Cont.cons u cont, t⟩


end Capless
