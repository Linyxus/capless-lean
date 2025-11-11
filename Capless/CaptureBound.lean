import Capless.CaptureSet
import Capless.Type
import Capless.Subcapturing

namespace Capless

inductive CaptureKind : Context n m k -> CaptureSet n k -> Kind -> Prop where
  | var : Context.Bound Γ x (S^C) -> CaptureKind Γ C K -> CaptureKind Γ {x=x} K
  | cvar : Context.CBound Γ c (.bound (.kind K)) -> CaptureKind Γ {c=c} K
  | sub : Kind.Subkind K L -> CaptureKind Γ C K -> CaptureKind Γ C L
  | union : CaptureKind Γ C1 K -> CaptureKind Γ C2 K -> CaptureKind Γ (C1 ∪ C2) K
  | empty : CaptureKind Γ .empty K

inductive CaptureBound : Context n m k -> CaptureSet n k -> CBound n k -> Prop where
  | subcapt: Subcapt Γ C1 C2 -> CaptureBound Γ C1 (CBound.upper C2)
  | subkind : CaptureKind Γ C K -> CaptureBound Γ C (CBound.kind K)
