import Capybara.Syntax
import Capybara.StaticSemantics.Subcapturing
namespace Capybara

mutual

inductive SSubtyping : Context n m k -> SType n m k -> SType n m k -> Prop
| top :
  SSubtyping Γ S ⊤
| refl :
  SSubtyping Γ S S
| trans :
  SSubtyping Γ S1 S2 ->
  SSubtyping Γ S2 S3 ->
  SSubtyping Γ S1 S3
| tvar :
  Context.LookupT Γ X (tparam S) ->
  SSubtyping Γ (SType.tvar X) S
| arrow :
  CSubtyping Γ T2 T1 ->
  ESubtyping (Γ,x:T2) E1 E2 ->
  SSubtyping Γ ((x:T1)->E1) ((x:T2)->E2)
| tarrow :
  SSubtyping Γ S2 S1 ->
  ESubtyping (Γ,X:tparam S2) E1 E2 ->
  SSubtyping Γ ([X<:S1]->E1) ([X<:S2]->E2)
| carrow :
  ESubtyping (Γ,c:cparam K) E1 E2 ->
  SSubtyping Γ ([c:K]->E1) ([c:K]->E2)
| talias_l :
  Context.LookupT Γ X (talias S) ->
  SSubtyping Γ (SType.tvar X) S
| talias_r :
  Context.LookupT Γ X (talias S) ->
  SSubtyping Γ S (SType.tvar X)

inductive CSubtyping : Context n m k -> CType n m k -> CType n m k -> Prop
| capt :
  SSubtyping Γ S1 S2 ->
  (Γ ⊢c C1 <: C2) ->
  CSubtyping Γ (S1^[m]C1) (S2^[m]C2)

inductive ESubtyping : Context n m k -> EType n m k -> EType n m k -> Prop
| type :
  CSubtyping Γ T1 T2 ->
  ESubtyping Γ (EType.type T1) (EType.type T2)
| ex :
  CSubtyping (Γ,c:cparam Kind.Fresh) T1 T2 ->
  ESubtyping Γ (EType.ex T1) (EType.ex T2)

end

end Capybara
