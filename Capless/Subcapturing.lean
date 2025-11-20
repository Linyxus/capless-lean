import Capless.Context
import Capless.CaptureSet

/-!

# Subcapturing

`Subcapt Γ C1 C2` defines the subcapturing judgement `Γ ⊢ C1 <: C2` in Fig. 2. Most rules correspond directly to the rules on the paper. The `Subcapt.cinstl` and `Subcapt.cinstr` rules are for capture set variables bound by `Term.bindc`--they are transparent in the subcapturing relation.
-/

namespace Capless

mutual
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
| proj :
  Subcapt Γ {s=s} C2 -> Subcapt Γ ({s=s}.proj K) (C2.proj K)
| proj_sub {C : CaptureSet n k} {K1 K2 : Kind}:
  K1.Subkind K2 -> Subcapt Γ (C.proj K1) (C.proj K2)
| proj_r : CaptureKind Γ C K -> Subcapt Γ C (C.proj K)
| proj_disj : Kind.Disjoint K1 K2 -> CaptureKind Γ C K1 -> Subcapt Γ (C.proj K2) .empty

inductive CaptureKind : Context n m k -> CaptureSet n k -> Kind -> Prop where
  -- | var : Context.Bound Γ x (S^C) -> CaptureKind Γ C K -> CaptureKind Γ {x=x} K
  | label : Context.LBound Γ x c S -> CaptureKind Γ {x=x} (.classifier c)
  | cvar : Context.CBound Γ c (.bound (.kind K)) -> CaptureKind Γ {c=c} K
  | csub : Subcapt Γ C1 C2 -> CaptureKind Γ C2 K -> CaptureKind Γ C1 K
  | sub : Kind.Subkind K L -> CaptureKind Γ C K -> CaptureKind Γ C L
  | empty : CaptureKind Γ .empty K
  | proj_kind {C : CaptureSet n k} : CaptureKind Γ (C.proj K) K
  | proj : CaptureKind Γ C K -> CaptureKind Γ (C.proj K1) K
end

theorem Subcapt.proj_l :  Subcapt Γ (C.proj K) C := by
  apply Subcapt.subset .proj_l


notation:50 Γ " ⊢ " C1 " <:c " C2 => Subcapt Γ C1 C2
notation:50 Γ " ⊢ " C " :k " K => CaptureKind Γ C K

end Capless
