import Capless.Context
import Capless.CaptureSet

/-!

# Subcapturing

`Subcapt Γ C1 C2` defines the subcapturing judgement `Γ ⊢ C1 <: C2` in Fig. 2. Most rules correspond directly to the rules on the paper. The `Subcapt.cinstl` and `Subcapt.cinstr` rules are for capture set variables bound by `Term.bindc`--they are transparent in the subcapturing relation.
-/

namespace Capless


inductive CaptureKind : Context n m k -> CaptureSet n k -> Kind -> Prop where
  | var : Context.Bound Γ x (S^C) -> CaptureKind Γ (C.proj L) K -> CaptureKind Γ {x=x | L} K
  | label : Context.LBound Γ x c S -> CaptureKind Γ {x=x|K} (K.intersect (.node c []))
  | cvar : Context.CBound Γ c (.bound (.kind K)) -> CaptureKind Γ {c=c|L} (L.intersect K)
  | cbound : Context.CBound Γ c (.bound (.upper C)) -> CaptureKind Γ (C.proj L) K -> CaptureKind Γ {c=c | L} K
  | cinstr : Context.CBound Γ c (.inst C) -> CaptureKind Γ (C.proj L) K -> CaptureKind Γ {c=c | L} K
  | sub : Kind.Subkind K L -> CaptureKind Γ C K -> CaptureKind Γ C L
  | empty : CaptureKind Γ .empty K
  | absurd : L.IsEmpty -> CaptureKind Γ (.singleton s L) K
  | union : CaptureKind Γ C1 K -> CaptureKind Γ C2 K -> CaptureKind Γ (C1 ∪ C2) K

inductive Subcapt : Context n m k -> CaptureSet n k -> CaptureSet n k -> Prop where
| trans :
  Subcapt Γ C1 C2 ->
  Subcapt Γ C2 C3 ->
  Subcapt Γ C1 C3
| subset :
  C1 ⊆ C2 ->
  Subcapt Γ C1 C2
| union :
  Subcapt Γ C1 C3 ->
  Subcapt Γ C2 C3 ->
  Subcapt Γ (C1 ∪ C2) C3
| var :
  Context.Bound Γ x (CType.capt C S) ->
  Subcapt Γ {x=x|L} (C.proj L)
| cinstl :
  Context.CBound Γ c (CBinding.inst C) ->
  Subcapt Γ (C.proj L) {c=c|L}
| cinstr :
  Context.CBound Γ c (CBinding.inst C) ->
  Subcapt Γ {c=c|L} (C.proj L)
| cbound :
  Context.CBound Γ c (CBinding.bound (CBound.upper C)) ->
  Subcapt Γ {c=c|L} (C.proj L)
| subkind : K.Subkind L -> Subcapt Γ (.singleton s K) (.singleton s L)
| proj_absurd : L.IsEmpty -> Subcapt Γ (.singleton s L) .empty
| proj_split : Subcapt Γ (.singleton s (.union K1 K2)) (.union (.singleton s K1) (.singleton s K2))

theorem Subcapt.proj_merge : Subcapt Γ (.union (.singleton s K1) (.singleton s K2)) (.singleton s (.union K1 K2)) := by
  apply union
  . apply subkind $ .union_rl (K2:=K2)
  . apply subkind .union_rr

notation:50 Γ " ⊢ " C1 " <:c " C2 => Subcapt Γ C1 C2
notation:50 Γ " ⊢ " C " :k " K => CaptureKind Γ C K

end Capless
