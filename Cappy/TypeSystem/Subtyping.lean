import Cappy.TypeSystem.Subcapturing
namespace Cappy

mutual

inductive CSubtyp : Context n m -> CType n m -> CType n m -> Prop where
| capt :
  Subcapt Γ C1 C2 ->
  SSubtyp Γ S1 S2 ->
  CSubtyp Γ (S1^C1) (S2^C2)

inductive SSubtyp : Context n m -> SType n m -> SType n m -> Prop where
| top :
  SSubtyp Γ S SType.top
| refl :
  SSubtyp Γ S S
| trans :
  SSubtyp Γ S1 S2 ->
  SSubtyp Γ S2 S3 ->
  SSubtyp Γ S1 S3
| tvar :
  Context.TBound Γ X S ->
  SSubtyp Γ (SType.tvar X) S
| boxed :
  CSubtyp Γ T1 T2 ->
  SSubtyp Γ (SType.boxed T1) (SType.boxed T2)
| arrow :
  CSubtyp Γ T2 T1 ->
  CSubtyp (Γ.var T2) U1 U2 ->
  SSubtyp Γ (∀(x:T1)U1) (SType.arrow a T2 U2)
| uarrow :
  CSubtyp (Γ.var T) U1 U2 ->
  SSubtyp Γ (∀(use x:T)U1) (∀(use x:T)U2)
| tarrow :
  SSubtyp Γ S2 S1 ->
  CSubtyp (Γ.tvar S2) T1 T2 ->
  SSubtyp Γ (∀[X<:S1]T1) (∀[X<:S2]T2)

end


end Cappy
