import Capless.Context
import Capless.CaptureSet
import Capless.ReachSet

/-!

# Subcapturing

`Subcapt Γ C1 C2` defines the subcapturing judgement `Γ ⊢ C1 <: C2` in Fig. 2. Most rules correspond directly to the rules on the paper. The `Subcapt.cinstl` and `Subcapt.cinstr` rules are for capture set variables bound by `Term.bindc`--they are transparent in the subcapturing relation.
-/

namespace Capless


inductive CaptureKind : Context n m k -> CaptureSet n k -> Kind -> Prop where
  | var : Context.Bound Γ x (S^C) -> CaptureKind Γ (C.proj L) K -> CaptureKind Γ {x=x | L} K
  | label : Context.LBound Γ x c S -> CaptureKind Γ {x=x|K} (.intersect (.node c []) K)
  | cvar : Context.CBound Γ c (.bound (.kind K)) -> CaptureKind Γ {c=c|L} (K.intersect L)
  | cbound : Context.CBound Γ c (.bound (.upper C)) -> CaptureKind Γ (C.proj L) K -> CaptureKind Γ {c=c | L} K
  | cinstr : Context.CBound Γ c (.inst C) -> CaptureKind Γ (C.proj L) K -> CaptureKind Γ {c=c | L} K
  | sub : Kind.Subkind K L -> CaptureKind Γ C K -> CaptureKind Γ C L
  | empty : CaptureKind Γ .empty K
  | singleton_absurd : K.IsEmpty -> CaptureKind Γ (.singleton s K) L
  | union : CaptureKind Γ C1 K -> CaptureKind Γ C2 K -> CaptureKind Γ (C1 ∪ C2) K
  | reach : CaptureKind Γ C K -> CaptureKind Γ C.with_reach K

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
| proj_r : CaptureKind Γ C K -> Subcapt Γ C (C.proj K)
| reach : Subcapt Γ C C.with_reach
| reachset :
  ReachSet Γ C R -> Subcapt Γ R C.with_reach

-- We don't need absurd here because...
theorem Subcapt.absurd (hk : CaptureKind Γ C K) (he : K.IsEmpty) : Subcapt Γ C .empty := by
  apply trans (.proj_r hk) (.subset $ .absurd he)

notation:50 Γ " ⊢ " C1 " <:c " C2 => Subcapt Γ C1 C2
notation:50 Γ " ⊢ " C " :k " K => CaptureKind Γ C K

end Capless
