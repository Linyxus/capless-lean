import Capless.Term
import Capless.Store
namespace Capless

inductive Reduce : State n m k -> State n' m' k' -> Prop where
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
| push_ex :
  Reduce
    ⟨σ, cont, Term.letex t u⟩
    ⟨σ, Cont.conse u cont, t⟩
| rename :
  Reduce
    ⟨σ, Cont.cons u cont, Term.var x⟩
    ⟨σ, cont, u.open x⟩
| rename_ex :
  Reduce
    ⟨σ, Cont.conse u cont, Term.pack c x⟩
    ⟨σ, cont, (u.open x).copen c⟩
| lift :
  (hv : Term.IsValue v) ->
  Reduce
    ⟨σ, Cont.cons u cont, v⟩
    ⟨σ.val v hv, cont.weaken, u⟩
| tlift :
  Reduce
    ⟨σ, Cont.cons u cont, Term.bindt S t⟩
    ⟨σ.tval S, cont.tweaken, t⟩
| clift :
  Reduce
    ⟨σ, Cont.cons u cont, Term.bindc C t⟩
    ⟨σ.cval C, cont.cweaken, t⟩

end Capless
