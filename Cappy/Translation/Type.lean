import Cappy.Translation.CaptureSet
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
  CaptureSet.Interp ρ Γ C D C' ->
  CType.Interp ρ Γ T D T' ->
  CType.Interp ρ Γ ((SType.boxed T)^C) D ((Capless.SType.box T')^C')

end Cappy
