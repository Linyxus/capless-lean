import Capless.Store
import Capless.Weakening.Typing
import Capless.Weakening.Subtyping
import Capless.Weakening.Subcapturing

/-!
# Typed Continuation Weakening for Capture Variables

This file proves weakening properties for typed continuations when extending contexts with
capture variables. It establishes that continuation typing judgments remain valid under
capture variable weakening operations.

## Key Results:

### Helper lemmas:
- Capture variable weakening commutation for effect types and capture sets
- Weakening relationships between different capture operations (`cweaken1_cweaken`, etc.)

### Well-scoping preservation:
- `WellScoped.cweaken`: Well-scoping is preserved under capture variable weakening

### Main weakening theorem:
- `TypedCont.cweaken`: Typed continuations remain valid when extending contexts with capture variables

The file handles the interaction between capture variables and all continuation forms,
ensuring that capture variable extensions preserve the validity of continuation typing
judgments. This is essential for soundness in the presence of capture-polymorphic abstractions.
-/

namespace Capless

theorem EType.cweaken_ex (T : CType n m (k+1)) :
  (EType.ex B T).cweaken = EType.ex B.cweaken T.cweaken1 := by
  simp [EType.cweaken, EType.crename, CType.cweaken1, CBound.cweaken]

-- theorem EType.cweaken_type (T : CType n m k) :
--   (EType.type T).cweaken = EType.type T.cweaken := by
--   simp [EType.cweaken, EType.crename, CType.cweaken]

theorem EType.cweaken_weaken (E : EType n m k) :
  E.weaken.cweaken = E.cweaken.weaken := by
  simp [EType.cweaken, EType.weaken, EType.crename_rename_comm]

theorem EType.cweaken1_weaken (E : EType n m (k+1)) :
  E.weaken.cweaken1 = E.cweaken1.weaken := by
  simp [EType.cweaken1, EType.weaken, EType.crename_rename_comm]

theorem CaptureSet.cweaken1_weaken (C : CaptureSet n (k+1)) :
  C.weaken.cweaken1 = C.cweaken1.weaken := by
  simp [CaptureSet.cweaken1, CaptureSet.weaken, CaptureSet.crename_rename_comm]

theorem EType.cweaken1_cweaken (E : EType n m k) :
  E.cweaken.cweaken1 = E.cweaken.cweaken := by
  simp [EType.cweaken1, EType.cweaken, EType.crename_crename]
  simp [FinFun.comp_weaken]

theorem CaptureSet.cweaken1_cweaken (C : CaptureSet n k) :
  C.cweaken.cweaken1 = C.cweaken.cweaken := by
  simp [CaptureSet.cweaken1, CaptureSet.cweaken, CaptureSet.crename_crename]
  simp [FinFun.comp_weaken]

theorem Cont.HasLabel.cweaken
  (h : Cont.HasLabel cont l tail) :
  Cont.HasLabel (cont.cweaken) l tail.cweaken := by
  induction h
  case here => simp [Cont.cweaken]; apply here
  case there_val => simp [Cont.cweaken]; apply there_val; aesop
  case there_tval => simp [Cont.cweaken]; apply there_tval; aesop
  case there_cval => simp [Cont.cweaken]; apply there_cval; aesop
  case there_label => simp [Cont.cweaken]; apply there_label; aesop
  case there_intercept => simp [Cont.cweaken]; apply there_intercept; aesop

theorem ReachSet.cweaken
  (hr : ReachSet Γ C R)
  : ReachSet (Γ.cvar b) C.cweaken R.cweaken := by
  induction hr
  case empty => constructor
  case union ha hb => apply! union
  case var hb hr ih =>
    have hb1 := hb.there_cvar (b:=b)
    apply var hb1
    rw [← CaptureSet.proj_crename]; exact ih
  case cinstr hb hr ih =>
    have hb1 := hb.there_cvar (b':=b)
    apply cinstr hb1
    rw [← CaptureSet.proj_crename]; exact ih
  case cbound hb hr ih =>
    have hb1 := hb.there_cvar (b':=b)
    apply cbound hb1
    rw [← CaptureSet.proj_crename]; exact ih
  case ckind hb =>
    have hb1 := hb.there_cvar (b':=b)
    apply ckind hb1
  case label hb =>
    have hb1 := hb.there_cvar (b:=b)
    apply label hb1
  case absurd he => apply! absurd

theorem WellScoped.cweaken
  (h : WellScoped Γ E Ct) :
  WellScoped (Γ.cvar b) E.cweaken Ct.cweaken := by
  induction h
  case empty => apply! empty
  case union ha hb => apply! union
  case ckind hb => apply! ckind hb.there_cvar
  case label hb hl => apply label hb.there_cvar hl.cweaken
  case label_disj hb hd => apply! label_disj hb.there_cvar
  case absurd => apply! absurd

theorem TypedCont.cweaken
  (h : TypedCont Γ Cin E t E' Ct) :
  TypedCont (Γ.cvar b) Cin.cweaken E.cweaken t.cweaken E'.cweaken Ct.cweaken := by
  induction h
  case none =>
    simp [Cont.cweaken]
    apply none
    apply? ESubtyp.cweaken
  case cons ht hs _ ih =>
    simp [Cont.cweaken, EType.cweaken_type]
    apply cons
    { have ht1 := ht.cweaken_ext (b := b)
      rw [EType.cweaken_weaken] at ht1
      rw [CaptureSet.weaken_crename]
      exact ht1 }
    { apply hs.cweaken }
    { exact ih }
  case conse ht hs _ ih =>
    simp [Cont.cweaken, EType.cweaken_ex]
    apply conse
    { have ht1 := ht.cweaken_cext_ext (b := b)
      rw [EType.cweaken1_weaken] at ht1
      rw [EType.cweaken1_cweaken] at ht1
      rw [CaptureSet.cweaken1_weaken] at ht1
      rw [CaptureSet.cweaken1_cweaken] at ht1
      exact ht1 }
    { apply hs.cweaken }
    { exact ih }
  case scope hb _ hs ih =>
    simp [Cont.cweaken]
    apply scope
    have hb1 := Context.LBound.there_cvar (b := b) hb
    exact hb1
    simp at ih
    apply ih
    have h := hs.cweaken (b:=b)
    aesop
  case intercept ht hsc hs h ih =>
    simp [Cont.cweaken]
    apply intercept
    { have ht1 := ht.cweaken_text_ext_ext (cb := b)
      simp [TBinding.cweaken, TBinding.crename, CType.cweaken, CType.crename,
            ← CaptureSet.proj_cweaken, CaptureSet.proj_crename,
            SType.weaken, SType.crename_rename_comm, SType.tweaken, ← SType.crename_trename_comm, SType.crename,
            CaptureSet.cweaken, ← CaptureSet.weaken_crename] at ht1
      simp [CaptureSet.cweaken, SType.tweaken, SType.weaken]
      exact ht1 }
    apply hsc.cweaken
    apply ih
    apply h.cweaken

end Capless
