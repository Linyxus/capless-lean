import Capless.Type.Core
namespace Capless

@[aesop safe [constructors, cases]]
inductive SType.IsValue : SType n m k -> Prop where
| xforall : SType.IsValue (SType.forall T U)
| tforall : SType.IsValue (SType.tforall S T)
| cforall : SType.IsValue (SType.cforall T)
| box : SType.IsValue (SType.box T)

@[aesop safe [constructors, cases]]
inductive CType.IsValue : CType n m k -> Prop where
| capt :
  (SType.IsValue S) ->
  CType.IsValue (CType.capt C S)

inductive SType.IsVar : SType n m k -> Prop where
| tvar : SType.IsVar (SType.tvar X)

end Capless
