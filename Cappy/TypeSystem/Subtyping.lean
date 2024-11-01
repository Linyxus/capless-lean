import Cappy.TypeSystem.Subcapturing
namespace Cappy

inductive SubAnnot : Annot -> Annot -> Prop where
| refl :
  SubAnnot a a
| use :
  SubAnnot Annot.eps Annot.use

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
  SubAnnot a1 a2 ->
  CSubtyp (Γ.var T) U1 U2 ->
  SSubtyp Γ (SType.arrow a1 T U1) (SType.arrow a2 T U2)
| tarrow :
  CSubtyp (Γ.tvar S) T1 T2 ->
  SSubtyp Γ (∀[X<:S]T1) (∀[X<:S]T2)

end


end Cappy
