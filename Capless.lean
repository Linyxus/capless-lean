/-
# Mechanisation of Capless

This is the entry of the mechanisation of System Capless.

## Syntax
-/
import «Capless».CaptureSet
import «Capless».Type
import «Capless».Term
import «Capless».Context

/-
## Static Semantics
-/
import «Capless».Subcapturing
import «Capless».Subtyping
import «Capless».Typing

/-
## Dynamic Semantics
-/
import «Capless».Store
import «Capless».Reduction

/-
## The First Layer of Substitution Theorems: Renaming
### Term Variable Renaming
-/
import «Capless».Renaming.Term.Subcapturing
import «Capless».Renaming.Term.Subtyping
import «Capless».Renaming.Term.Typing
/-
### Type Variable Renaming
-/
import «Capless».Renaming.Type.Subcapturing
import «Capless».Renaming.Type.Subtyping
import «Capless».Renaming.Type.Typing
/-
### Capture Variable Renaming
-/
import «Capless».Renaming.Capture.Subcapturing
import «Capless».Renaming.Capture.Subtyping
import «Capless».Renaming.Capture.Typing

/-
## The Second Layer of Substitution Theorems: Substitution
### Term Variable Substitution
-/
import «Capless».Subst.Term.Subcapturing
import «Capless».Subst.Term.Subtyping
import «Capless».Subst.Term.Typing
/-
### Type Variable Substitution
-/
import «Capless».Subst.Type.Subcapturing
import «Capless».Subst.Type.Subtyping
import «Capless».Subst.Type.Typing
/-
### Capture Variable Substitution
-/
import «Capless».Subst.Capture.Subcapturing
import «Capless».Subst.Capture.Subtyping
import «Capless».Subst.Capture.Typing

/-
## Inversion Theorems
### Store Lookup
It is mainly composed of the following results:
- The type of the value stored in the store matches that in the corresponding typing context.
-/
import «Capless».Inversion.Lookup
/-
### Subtyping
-/
import «Capless».Inversion.Subtyping
/-
### Typing
Main results:
- Inversion of redex typing. For instance, an application `x y `is well-typed implies
  that x is typed at a function and y can be typed at the argument type of the function.
-/
import «Capless».Inversion.Typing

/-
## Soundness
The standard progress and preservation theorems.
-/
import «Capless».Soundness.Preservation
import «Capless».Soundness.Progress
