/-
# Mechanisation of System Capless

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
## Renaming Context Morphisms
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
## Substitution Context Morphisms
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
-/
import «Capless».Inversion.Lookup
/-
### Subtyping
-/
import «Capless».Inversion.Subtyping
/-
### Typing
-/
import «Capless».Inversion.Typing

/-
## Soundness
The standard progress and preservation theorems.
-/
import «Capless».Soundness.Preservation
import «Capless».Soundness.Progress
