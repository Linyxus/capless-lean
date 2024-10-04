import Capless.Term
import Capless.Store
namespace Capless

@[aesop unsafe [constructors 50%]]
inductive Reduce : State n m k -> State n' m' k' -> Prop where
| apply {σ : Store n m k} :
  σ.Bound x (Term.lam T t) ->
  Reduce ⟨σ, cont, Term.app x y⟩ ⟨σ, cont, t.open y⟩
| tapply {σ : Store n m k} :
  σ.Bound x (Term.tlam S t) ->
  Reduce ⟨σ, cont, Term.tapp x X⟩ ⟨σ, cont, t.topen X⟩
| capply {σ : Store n m k} :
  σ.Bound x (Term.clam t) ->
  Reduce ⟨σ, cont, Term.capp x c⟩ ⟨σ, cont, t.copen c⟩
| unbox {σ : Store n m k} :
  σ.Bound x (Term.boxed y) ->
  Reduce ⟨σ, cont, Term.unbox C x⟩ ⟨σ, cont, Term.var y⟩
| enter :
  Reduce
    ⟨σ, cont, boundary:S in t⟩
    ⟨(σ.label S).cval {x=0}, cont.weaken.cweaken.scope 0, t⟩
| leave_var :
  Reduce
    ⟨σ, cont.scope x, Term.var y⟩
    ⟨σ, cont, Term.var y⟩
| leave_val {v : Term n m k} :
  (hv : Term.IsValue v) ->
  Reduce
    ⟨σ, cont.scope x, v⟩
    ⟨σ, cont, v⟩
| invoke {σ : Store n m k} {cont : Cont n m k} :
  σ.LBound x S ->
  cont.HasLabel x tail ->
  Reduce
    ⟨σ, cont, Term.invoke x y⟩
    ⟨σ, tail, Term.var y⟩
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
| lift :
  (hv : Term.IsValue v) ->
  Reduce
    ⟨σ, Cont.cons u cont, v⟩
    ⟨σ.val v hv, cont.weaken, u⟩
| lift_ex :
  Reduce
    ⟨σ, Cont.conse u cont, Term.pack C x⟩
    ⟨σ.cval C, cont.cweaken, u.open x⟩
| tlift :
  Reduce
    ⟨σ, cont, Term.bindt S t⟩
    ⟨σ.tval S, cont.tweaken, t⟩
| clift :
  Reduce
    ⟨σ, cont, Term.bindc C t⟩
    ⟨σ.cval C, cont.cweaken, t⟩

end Capless
