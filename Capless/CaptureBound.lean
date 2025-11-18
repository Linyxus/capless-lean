import Capless.CaptureSet
import Capless.Type
import Capless.Subcapturing

namespace Capless

inductive CaptureBound : Context n m k -> CaptureSet n k -> CBound n k -> Prop where
  | subcapt: Subcapt Γ C1 C2 -> CaptureBound Γ C1 (CBound.upper C2)
  | subkind : CaptureKind Γ C K -> CaptureBound Γ C (CBound.kind K)
