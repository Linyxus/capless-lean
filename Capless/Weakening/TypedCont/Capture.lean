import Capless.Store
import Capless.Weakening.Typing
import Capless.Weakening.Subtyping
namespace Capless

theorem EType.cweaken_ex (T : CType n m (k+1)) :
  (EType.ex T).cweaken = EType.ex T.cweaken1 := by
  simp [EType.cweaken, EType.crename, CType.cweaken1]

theorem EType.cweaken_type (T : CType n m k) :
  (EType.type T).cweaken = EType.type T.cweaken := by
  simp [EType.cweaken, EType.crename, CType.cweaken]

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

theorem WellScoped.cweaken
  (h : WellScoped Γ E Ct) :
  WellScoped (Γ.cvar b) E.cweaken Ct.cweaken := by
  induction h
  case empty => constructor
  case union ih1 ih2 => apply union <;> aesop
  case singleton hb _ ih =>
    apply singleton
    { have hb1 := Context.Bound.there_cvar (b := b) hb
      simp [CType.cweaken, CType.crename] at hb1
      exact hb1 }
    { exact ih }
  case csingleton hb _ ih =>
    apply csingleton
    { have hb1 := Context.CBound.there_cvar (b' := b) hb
      simp [CType.cweaken, CType.crename] at hb1
      exact hb1 }
    { exact ih }
  case label hb hs =>
    apply label
    { have hb1 := Context.LBound.there_cvar (b := b) hb
      simp [CType.cweaken, CType.crename] at hb1
      exact hb1 }
    { apply hs.cweaken }

theorem TypedCont.cweaken
  (h : TypedCont Γ E t E' Ct) :
  TypedCont (Γ.cvar b) E.cweaken t.cweaken E'.cweaken Ct.cweaken := by
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

end Capless
