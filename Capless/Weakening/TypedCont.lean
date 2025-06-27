import Capless.Weakening.TypedCont.Term
import Capless.Weakening.TypedCont.Type
import Capless.Weakening.TypedCont.Capture

/-!
# Typed Continuation Weakening

This file provides a unified import for all weakening operations related to typed continuations
in the Capless type system. It aggregates the weakening properties for continuations under
different types of context extensions.

The file imports:
- `TypedCont.Term`: Weakening for term variable extensions
- `TypedCont.Type`: Weakening for type variable extensions
- `TypedCont.Capture`: Weakening for capture variable extensions

Together, these modules ensure that typed continuation judgments are preserved under all forms
of context weakening, which is essential for the soundness of the continuation-based semantics.
-/
