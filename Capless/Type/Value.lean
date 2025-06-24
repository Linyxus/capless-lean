import Capless.Type.Core
namespace Capless

/-!
# Value Type Predicates

`SType.IsValue` and `CType.IsValue` are predicates for identifying value types. `SType.IsVar` checks whether a type is a type variable.
-/

@[aesop safe [constructors, cases]]
inductive SType.IsValue : SType n m k -> Prop where
| xforall : SType.IsValue (∀(x:T)U)
| tforall : SType.IsValue (∀[X<:S]T)
| cforall : SType.IsValue (∀[c<:B]T)
| box : SType.IsValue (□ T)

@[aesop safe [constructors, cases]]
inductive CType.IsValue : CType n m k -> Prop where
| capt :
  S.IsValue ->
  CType.IsValue (S^C)

inductive SType.IsVar : SType n m k -> Prop where
| tvar : SType.IsVar (SType.tvar X)

end Capless
