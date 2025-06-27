import Capless.Store
import Capless.Weakening.Typing
import Capless.Weakening.Subtyping
import Capless.Weakening.Subcapturing

/-!
# Typed Continuation Weakening for Type Variables

This file proves weakening properties for typed continuations when extending contexts with
type variables. It shows that continuation typing judgments are preserved under type variable
weakening operations.

## Key Results:

### Helper lemmas:
- Type variable weakening commutation for effect types (`EType.tweaken_ex`, `EType.tweaken_weaken`, etc.)
- Label preservation under type weakening for continuations

### Well-scoping preservation:
- `WellScoped.tweaken`: Well-scoping is preserved under type variable weakening

### Main weakening theorem:
- `TypedCont.tweaken`: Typed continuations remain valid when extending contexts with type variables

The weakening handles all continuation constructs (empty, value-consuming, existential, and scoped)
and ensures that type variable extensions do not invalidate existing continuation typing judgments.
This is crucial for maintaining soundness when type abstractions are introduced.
-/

namespace Capless

theorem EType.tweaken_ex (T : CType n m (k+1)) :
  (EType.ex T).tweaken = EType.ex T.tweaken := by
  simp [EType.tweaken, EType.trename, CType.tweaken]

-- theorem EType.tweaken_type (T : CType n m k) :
--   (EType.type T).tweaken = EType.type T.tweaken := by
--   simp [EType.tweaken, EType.trename, CType.tweaken]

theorem EType.tweaken_weaken (E : EType n m k) :
  E.weaken.tweaken = E.tweaken.weaken := by
  simp [EType.tweaken, EType.weaken, EType.trename_rename_comm]

theorem EType.tweaken_cweaken (E : EType n m k) :
  E.cweaken.tweaken = E.tweaken.cweaken := by
  simp [EType.tweaken, EType.cweaken, EType.crename_trename_comm]

theorem Cont.HasLabel.tweaken
  (h : Cont.HasLabel cont x tail) :
  Cont.HasLabel cont.tweaken x tail.tweaken := by
  induction h
  case here => simp [Cont.tweaken]; apply here
  case there_val ih => simp [Cont.tweaken]; apply there_val; trivial
  case there_tval => simp [Cont.tweaken]; apply there_tval; aesop
  case there_cval => simp [Cont.tweaken]; apply there_cval; aesop
  case there_label => simp [Cont.tweaken]; apply there_label; aesop

theorem WellScoped.tweaken
  (h : WellScoped Γ cont Ct) :
  WellScoped (Γ.tvar b) cont.tweaken Ct := by
  induction h
  case empty => constructor
  case union ih1 ih2 => apply union <;> aesop
  case singleton hb _ ih =>
    apply singleton
    { have hb1 := Context.Bound.there_tvar (b := b) hb
      simp [CType.tweaken, CType.trename] at hb1
      exact hb1 }
    { exact ih }
  case csingleton hb _ ih =>
    apply csingleton
    { have hb1 := Context.CBound.there_tvar (b' := b) hb
      simp [CType.tweaken, CType.trename] at hb1
      exact hb1 }
    { exact ih }
  case cbound hb _ ih =>
    apply cbound
    { have hb1 := Context.CBound.there_tvar (b' := b) hb
      simp [CType.tweaken, CType.trename] at hb1
      exact hb1 }
    { exact ih }
  case label hb hs =>
    apply label
    { have hb1 := Context.LBound.there_tvar (b := b) hb
      simp [CType.tweaken, CType.trename] at hb1
      exact hb1 }
    { apply hs.tweaken }

theorem TypedCont.tweaken
  (h : TypedCont Γ E t E' C0) :
  TypedCont (Γ.tvar S) E.tweaken t.tweaken E'.tweaken C0 := by
  induction h
  case none =>
    simp [Cont.tweaken]
    apply none
    apply? ESubtyp.tweaken
  case cons ht hs _ ih =>
    simp [Cont.tweaken]
    -- simp [EType.tweaken_type]
    apply cons
    { have ht1 := ht.tweaken_ext (b := S)
      rw [EType.tweaken_weaken] at ht1
      exact ht1 }
    { apply hs.tweaken }
    { exact ih }
  case conse ht hs _ ih =>
    simp [Cont.tweaken]
    simp [EType.tweaken_ex]
    apply conse
    { have ht1 := ht.tweaken_cext_ext (b := S)
      rw [EType.tweaken_weaken] at ht1
      rw [EType.tweaken_cweaken] at ht1
      exact ht1 }
    { apply hs.tweaken }
    { exact ih }
  case scope hb _ hs ih =>
    simp [Cont.tweaken]
    apply scope
    have hb1 := Context.LBound.there_tvar (b := S) hb
    exact hb1
    simp at ih
    apply ih
    have h := hs.tweaken (b:=S)
    aesop

end Capless
