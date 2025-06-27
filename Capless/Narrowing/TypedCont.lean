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
  (h : TypedCont Γ E1 cont E C0)
  (hsub : ESubtyp Γ E2 E1) :
  TypedCont Γ E2 cont E C0 := by
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

end Capless
