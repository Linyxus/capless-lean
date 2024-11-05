import Capless.Type
namespace Capless

/-!
# Anchoring
!-/

inductive CaptureSet.AnchorCapture : CaptureSet n (k+1) -> CaptureSet n k -> CaptureSet n (k+1) -> Prop where
| anchor {C : CaptureSet n k} :
  CaptureSet.AnchorCapture (C.cweaken ∪ {c=0}) C' (C'.cweaken ∪ {c=0})
| anchor_devoid {C : CaptureSet n k} :
  CaptureSet.AnchorCapture C.cweaken C' C'.cweaken

inductive EType.AnchorCapture : EType n m (k+1) -> CaptureSet n k -> EType n m (k+1) -> Prop where
| ex :
  EType.AnchorCapture (EType.ex T) C (EType.ex T)
| type :
  CaptureSet.AnchorCapture C C' C'' ->
  EType.AnchorCapture (EType.type (S^C)) C' (EType.type (S^C''))

inductive EType.AnchorType : EType n (m+1) k -> CaptureSet n k -> EType n (m+1) k -> Prop where
| ex :
  EType.AnchorType (EType.ex T) C (EType.ex T)
| type :
  EType.AnchorType (EType.type (S^C)) C' (EType.type (S^C'))

inductive SType.AnchorUniversal : SType n m k -> CaptureSet n k -> SType n m k -> Prop where
| top :
  SType.AnchorUniversal SType.top C SType.top
| tvar :
  SType.AnchorUniversal (SType.tvar X) C (SType.tvar X)
| arrow :
  SType.AnchorUniversal (∀(x:T)U) C (∀(x:T)U)
| tarrow :
  EType.AnchorType E C E' ->
  SType.AnchorUniversal (∀[X<:S]E) C (∀[X<:S]E')
| carrow :
  EType.AnchorCapture E C E' ->
  SType.AnchorUniversal (∀[c]E) C (∀[c]E')
| box :
  SType.AnchorUniversal (SType.box T) C (SType.box T)

inductive SType.Anchor : SType n m k -> CaptureSet n k -> CType n m k -> Prop where
| capt :
  SType.AnchorUniversal S C' S' ->
  SType.Anchor S C' (S'^C')

end Capless
