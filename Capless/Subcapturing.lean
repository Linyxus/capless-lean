import Capless.Context
import Capless.CaptureSet

/-!

# Subcapturing

`Subcapt Γ C1 C2` defines the subcapturing judgement `Γ ⊢ C1 <: C2` in Fig. 2. Most rules correspond directly to the rules on the paper. The `Subcapt.cinstl` and `Subcapt.cinstr` rules are for capture set variables bound by `Term.bindc`--they are transparent in the subcapturing relation.
-/

namespace Capless


inductive CaptureKind : Context n m k -> CaptureSet n k -> Kind -> Prop where
  | var : Context.Bound Γ x (S^C) -> CaptureKind Γ C K -> CaptureKind Γ {x=x} K
  | label : Context.LBound Γ x c S -> CaptureKind Γ {x=x} (.singleton c [])
  | cvar : Context.CBound Γ c (.bound (.kind K)) -> CaptureKind Γ {c=c} K
  | cbound : Context.CBound Γ c (.bound (.upper C)) -> CaptureKind Γ C K -> CaptureKind Γ {c=c} K
  | cinstr : Context.CBound Γ c (.inst C) -> CaptureKind Γ C K -> CaptureKind Γ {c=c} K
  | sub : Kind.Subkind K L -> CaptureKind Γ C K -> CaptureKind Γ C L
  | empty : CaptureKind Γ .empty K
  | singleton_proj_kind : CaptureKind Γ (.singleton $ .proj s K) K
  | singleton_proj : CaptureKind Γ (.singleton s) K -> CaptureKind Γ (.singleton $ s.proj K1) K
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
  Subcapt Γ {x=x} C
| cinstl :
  Context.CBound Γ c (CBinding.inst C) ->
  Subcapt Γ C {c=c}
| cinstr :
  Context.CBound Γ c (CBinding.inst C) ->
  Subcapt Γ {c=c} C
| cbound :
  Context.CBound Γ c (CBinding.bound (CBound.upper C)) ->
  Subcapt Γ {c=c} C
| singleton_proj_sub {s : Singleton n k} {K1 K2 : Kind}:
  K1.Subkind K2 -> Subcapt Γ (.singleton $ s.proj K1) (.singleton $ s.proj K2)
| singleton_proj_l : Subcapt Γ (.singleton $ .proj s K) (.singleton s)
| singleton_proj : Subcapt Γ (.singleton s) C -> Subcapt Γ (.singleton $ s.proj K) (C.proj K)
| singleton_proj_disj :
  Kind.Disjoint K1 K2 ->
  CaptureKind Γ (.singleton s) K1 ->
  Subcapt Γ (.singleton $ s.proj K2) .empty


notation:50 Γ " ⊢ " C1 " <:c " C2 => Subcapt Γ C1 C2
notation:50 Γ " ⊢ " C " :k " K => CaptureKind Γ C K

end Capless
