import Capless.Context
import Capless.Subcapturing
import Capless.Type

namespace Capless

mutual

inductive ESubtyp : Context n m k -> EType n m k -> EType n m k -> Prop where
| exist :
  CSubtyp (Context.cvar Γ CBinding.bound) T1 T2 ->
  ESubtyp Γ (EType.ex T1) (EType.ex T2)
| existp_erase :
  CSubtyp (Context.cvar Γ CBinding.bound) T T' ->
  -- ^ Transitivity needs to be encoded manually
  ESubtyp Γ (EType.exp c T) (EType.ex T')
| type :
  CSubtyp Γ T1 T2 ->
  ESubtyp Γ (EType.type T1) (EType.type T2)

inductive CSubtyp : Context n m k -> CType n m k -> CType n m k -> Prop where
| capt :
  Subcapt Γ C1 C2 ->
  SSubtyp Γ S1 S2 ->
  CSubtyp Γ (CType.capt C1 S1) (CType.capt C2 S2)

inductive SSubtyp : Context n m k -> SType n m k -> SType n m k -> Prop where
| top :
  SSubtyp Γ S SType.top
| refl :
  SSubtyp Γ S S
| trans :
  SSubtyp Γ S1 S2 ->
  SSubtyp Γ S2 S3 ->
  SSubtyp Γ S1 S3
| tvar :
  Context.TBound Γ X (TBinding.bound S) ->
  SSubtyp Γ (SType.tvar X) S
| tinstl :
  Context.TBound Γ X (TBinding.inst S) ->
  SSubtyp Γ S (SType.tvar X)
| tinstr :
  Context.TBound Γ X (TBinding.inst S) ->
  SSubtyp Γ (SType.tvar X) S
| boxed :
  CSubtyp Γ T1 T2 ->
  SSubtyp Γ (SType.box T1) (SType.box T2)
| xforall :
  CSubtyp Γ E2 E1 ->
  ESubtyp (Context.var Γ E2) F1 F2 ->
  SSubtyp Γ (SType.forall E1 F1) (SType.forall E2 F2)
| tforall :
  SSubtyp Γ S2 S1 ->
  ESubtyp (Context.tvar Γ (TBinding.bound S2)) E1 E2 ->
  SSubtyp Γ (SType.tforall S1 E1) (SType.tforall S2 E2)
| cforall :
  ESubtyp (Context.cvar Γ CBinding.bound) E1 E2 ->
  SSubtyp Γ (SType.cforall E1) (SType.cforall E2)

end

end Capless
