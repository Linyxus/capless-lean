import Cappy.Translation.Encoding.CaptureSet
import Capless.Type
namespace Cappy

/-!
# Encoding of Types
!-/

inductive CType.Interp : TMap n m k -> Context n m -> CType n m -> Capless.CaptureSet n k -> Capless.CType n m k -> Prop where
| i_top :
  CaptureSet.Interp ρ Γ C D C' ->
  CType.Interp ρ Γ (SType.top^C) D (⊤^C')
| i_tvar :
  CaptureSet.Interp ρ Γ C D C' ->
  CType.Interp ρ Γ ((SType.tvar X)^C) D ((Capless.SType.tvar X)^C')
| i_boxed :
  CType.Interp ρ Γ T D T' ->
  CType.Interp ρ Γ
     ((SType.boxed T)^{})
     D
     ((∀(x:⊤^{})((∀(x:⊤^{})(Capless.EType.type T'.weaken.weaken))^Capless.CaptureSet.empty))^Capless.CaptureSet.empty)
| i_arrow :
  CaptureSet.Interp ρ Γ C D C' ->
  CType.Interp ρ.cweaken Γ T ({c=0}) T' ->
  CaptureSet.Interp ρ.ext (Γ.var T) ({x*=0}∪{x=0}) {} D1 ->
  CType.Interp ρ.ext (Γ.var T) U (D.weaken.cweaken ∪ D1) U' ->
  CType.Interp ρ Γ
    ((∀(x:T)U)^C)
    D
    ((∀[c](Capless.EType.type (∀(x:T')U')^(C'.cweaken)))^({}))
| i_uarrow :
  CaptureSet.Interp ρ Γ C D C' ->
  CType.Interp ρ.cweaken Γ T ({c=0}) T' ->
  CaptureSet.Interp ρ.ext (Γ.var T) ({x*=0}∪{x=0}) {} D1 ->
  CType.Interp ρ.ext (Γ.var T) U (D.weaken.cweaken ∪ D1) U' ->
  CType.Interp ρ Γ
    ((∀(use x:T)U)^C)
    D
    ((∀[c](Capless.EType.type (∀(x:T')U')^(C'.cweaken ∪ {c=0})))^({}))
| i_tarrow :
  CaptureSet.Interp ρ Γ C D C' ->
  CType.Interp ρ.cweaken Γ (S^{}) ({c=0}) (S'^{}) ->
  CType.Interp ρ.text (Γ.tvar S) T (D.cweaken ∪ {c=0}) T' ->
  CType.Interp ρ Γ
    ((∀[X<:S]T)^C)
    D
    ((∀[c](Capless.EType.type (∀[X<:S']T')^(C'.cweaken)))^({}))

end Cappy
