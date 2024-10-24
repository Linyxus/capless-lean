import Capless.Context
import Capless.Basic
import Cappy.Translation.TMap
namespace Cappy

structure TContext (n m k : Nat) where
  ctx : Capless.Context n m k
  map : TMap n m k

end Cappy
