import Capless.Tactics
import Capless.Store
import Capless.Subtyping.Basic
import Capless.Narrowing.Typing

/-!
# Narrowing Lemma for Continuation Typing

This file provides the narrowing lemma for typed continuation stacks (`TypedCont`).
Continuation typing describes how values flow through evaluation contexts in the
operational semantics, capturing the types of intermediate computations.

## Main Result

- `TypedCont.narrow`: If `TypedCont Γ E1 cont E C` and `E2 <: E1`, then
  `TypedCont Γ E2 cont E C`

This lemma states that if a continuation stack can handle inputs of type `E1` and
produce outputs of type `E`, then it can also handle inputs of any subtype `E2` of `E1`.
This is crucial for type safety - it ensures that when we have more specific information
about the input type, the continuation stack remains well-typed.

The proof proceeds by case analysis on the continuation structure, utilizing the
transitivity of subtyping and the narrowing properties of the underlying typing relation.
-/

namespace Capless

theorem TypedCont.narrow
  (h : TypedCont Γ E1 Cin cont E C0)
  (hsub : ESubtyp Γ E2 E1) :
  TypedCont Γ E2 Cin cont E C0 := by
  cases h
  case none =>
    apply TypedCont.none
    apply? ESubtyp.trans
  case cons =>
    cases hsub
    rename_i hsub
    apply TypedCont.cons
    { apply! Typed.narrow }
    { trivial }
    { trivial }
  case conse =>
    cases hsub
    rename_i hsub
    apply TypedCont.conse
    { apply! Typed.narrow }
    { trivial }
    { trivial }
  case scope =>
    cases hsub
    rename_i hsub
    apply TypedCont.scope
    { assumption }
    { assumption }
    { apply CSubtyp.trans <;> aesop }
  case intercept =>
    cases hsub
    rename_i hsub
    apply TypedCont.intercept
    assumption
    assumption
    assumption
    apply! CSubtyp.trans

theorem TypedCont.cin_narrow
  (h : TypedCont Γ E1 Cin1 cont E C0)
  (hsub : Γ ⊢ Cin2 <:c Cin1)
  : TypedCont Γ E1 Cin2 cont E C0 := by
  cases h
  case none => apply! TypedCont.none
  case cons ht hsc h =>
    apply cons ht hsc $ h.cin_narrow _
    apply Subcapt.join hsub .rfl
  case conse ht hsc h =>
    apply conse ht hsc $ h.cin_narrow _
    apply Subcapt.join hsub .rfl
  case scope hb hs h =>
    apply scope hb _ hs
    apply h.cin_narrow hsub
  case intercept hws hsub_T0 htyped htcont =>
    -- From the error, we can see the actual types:
    -- K✝ : Kind (the classifier kind)
    -- hws : WellScoped Γ cont Ct
    -- hsub_T0 : Γ ⊢ T0 <: S^{}
    -- htyped : Typed (((Γ,X<:⊤),x:(Label[.tvar 0]^(Cin1.proj K))),x:(SType.tvar 0)^{}) h ...
    -- htcont : TypedCont Γ (S^{}) (Cin1 ∪ Ct) cont E' C
    -- Order of inaccessibles: Kind, CaptureSet, CaptureSet, Term, Cont, CType, SType
    rename_i Kd _ _ _ _ _ _  -- Get all 7 inaccessibles, Kd should be Kind
    apply intercept
    { -- use Typed.narrow in the middle for the label
      -- htyped : Typed (((Γ,X<:⊤),x:(Label[.tvar 0]^(Cin1.proj Kd))),x:(SType.tvar 0)^{}) h ...
      -- goal : Typed (((Γ,X<:⊤),x:(Label[.tvar 0]^(Cin2.proj Kd))),x:(SType.tvar 0)^{}) h ...
      -- The difference is in the MIDDLE binding (position 1), not the outer one (position 0)
      -- Step 1: Build the subtyping on capture sets
      have hsub_proj : Subcapt Γ (Cin2.proj Kd) (Cin1.proj Kd) := Subcapt.apply_proj hsub
      have hsub_proj' : Subcapt (Γ,X<:⊤) (Cin2.proj Kd) (Cin1.proj Kd) := hsub_proj.tweaken
      -- Step 2: Build the CSubtyp for the label types
      have hcsub : CSubtyp (Γ,X<:⊤) (Label[.tvar 0]^(Cin2.proj Kd)) (Label[.tvar 0]^(Cin1.proj Kd)) :=
        CSubtyp.capt hsub_proj' SSubtyp.refl
      -- Step 3: Use VarSubst.narrow extended with VarSubst.ext to narrow position 1
      -- The VarSubst.ext needs the outer type to be the same in source and target
      -- VarSubst.narrow gives: VarSubst ((Γ,X<:⊤),x:T1) id ((Γ,X<:⊤),x:T2)
      -- VarSubst.ext extends with the same outer binding
      have hnarrow := VarSubst.narrow hcsub
      have hsubst := VarSubst.ext hnarrow ((SType.tvar 0)^{})
      have h := Typed.subst htyped hsubst
      -- Simplify the FinFun.id.ext to id
      simp only [FinFun.id_ext, Term.rename_id, EType.rename_id, CaptureSet.rename_id] at h
      exact h }
    assumption
    apply htcont.cin_narrow $ Subcapt.join hsub .rfl
    assumption




end Capless
