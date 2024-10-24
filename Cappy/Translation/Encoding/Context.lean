import Cappy.Translation.Encoding.Type
import Cappy.Translation.TContext
namespace Cappy

inductive Context.Interp : Context n m -> TContext n m k -> Prop where
| empty :
  Context.Interp empty TContext.empty

end Cappy
