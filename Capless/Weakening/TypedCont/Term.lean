import Capless.Store
import Capless.Weakening.Typing
import Capless.Weakening.Subtyping
import Capless.Weakening.Subcapturing
namespace Capless

theorem EType.weaken1_weaken (E : EType n m k) :
  E.weaken.weaken1 = E.weaken.weaken := by
  simp [EType.weaken, EType.weaken1, EType.rename_rename]
  rw [<- FinFun.comp_weaken]

theorem CaptureSet.weaken1_weaken (C : CaptureSet n k) :
  C.weaken.weaken1 = C.weaken.weaken := by
  simp [CaptureSet.weaken, CaptureSet.weaken1, CaptureSet.rename_rename]
  rw [<- FinFun.comp_weaken]

theorem EType.weaken_ex (T : CType n m (k+1)) :
  (EType.ex T).weaken = EType.ex T.weaken := by
  simp [EType.weaken, EType.rename, CType.weaken]

theorem EType.weaken_cweaken (E : EType n m k) :
  E.cweaken.weaken = E.weaken.cweaken := by
  simp [EType.weaken, EType.cweaken, EType.crename_rename_comm]

theorem CaptureSet.weaken_cweaken (C : CaptureSet n k) :
  C.cweaken.weaken = C.weaken.cweaken := by
  simp [CaptureSet.weaken, CaptureSet.cweaken, CaptureSet.crename_rename_comm]

theorem Cont.HasLabel.weaken
  (h : Cont.HasLabel cont x tail) :
  Cont.HasLabel cont.weaken x.succ tail.weaken := by
  induction h
  case here =>
    simp [Cont.weaken]
    apply here
  case there_val ih =>
    simp [Cont.weaken]
    apply there_val; trivial
  case there_tval ih =>
    simp [Cont.weaken]
    apply there_tval; trivial
  case there_cval ih =>
    simp [Cont.weaken]
    apply there_cval; trivial
  case there_label ih =>
    simp [Cont.weaken]
    apply there_label; trivial

theorem WellScoped.weaken
  (h : WellScoped Γ cont Ct) :
  WellScoped (Γ.var T) cont.weaken Ct.weaken := by
  induction h
  case empty => simp [CaptureSet.weaken]; constructor
  case union ih1 ih2 =>
    simp [CaptureSet.weaken] at *
    apply union <;> aesop
  case singleton hb _ ih =>
    apply singleton
    { simp [FinFun.weaken]
      have hb1 := Context.Bound.there_var (E':=T) hb
      simp [CType.weaken, CType.rename] at hb1
      exact hb1 }
    { exact ih }
  case csingleton hb _ ih =>
    apply csingleton
    { have hb1 := Context.CBound.there_var (E:=T) hb
      exact hb1 }
    { exact ih }
  case label hb hs =>
    apply label
    { have hb1 := Context.LBound.there_var (E:=T) hb
      exact hb1 }
    { apply hs.weaken }

theorem TypedCont.weaken
  (h : TypedCont Γ E t E' C0) :
  TypedCont (Γ.var T) E.weaken t.weaken E'.weaken C0.weaken := by
  induction h
  case none =>
    simp [Cont.weaken]
    apply none
    apply? ESubtyp.weaken
  case cons ih =>
    simp [Cont.weaken]
    have heq : ∀ {n m k} {T0 : CType n m k}, (EType.type T0).weaken = EType.type T0.weaken := by
      intro T0
      simp [EType.weaken, EType.rename, CType.weaken]
    rw [heq]
    apply cons
    { rename_i ht _ _
      have ht1 := ht.weaken_ext (P := T)
      rw [EType.weaken1_weaken] at ht1
      rw [CaptureSet.weaken1_weaken] at ht1
      exact ht1 }
    { apply WellScoped.weaken; assumption }
    { exact ih }
  case conse ih =>
    simp [Cont.weaken, EType.weaken_ex]
    apply conse
    { rename_i ht _ _
      have ht1 := ht.weaken_cext_ext (P := T)
      rw [EType.weaken1_weaken] at ht1
      rw [EType.weaken_cweaken] at ht1
      rw [CaptureSet.weaken1_weaken] at ht1
      rw [CaptureSet.weaken_cweaken] at ht1
      exact ht1 }
    { apply WellScoped.weaken; aesop }
    { exact ih }
  case scope hs ih =>
    simp [Cont.weaken]
    apply scope
    { constructor; aesop }
    { aesop }
    { apply hs.weaken }

theorem Cont.HasLabel.lweaken
  (h : Cont.HasLabel cont x tail) :
  Cont.HasLabel cont.weaken x.succ tail.weaken := by
  induction h
  case here =>
    simp [Cont.weaken]
    apply here
  case there_val ih =>
    simp [Cont.weaken]
    apply there_val; trivial
  case there_tval ih =>
    simp [Cont.weaken]
    apply there_tval; trivial
  case there_cval ih =>
    simp [Cont.weaken]
    apply there_cval; trivial
  case there_label ih =>
    simp [Cont.weaken]
    apply there_label; trivial

theorem WellScoped.lweaken
  (h : WellScoped Γ cont Ct) :
  WellScoped (Γ.label S) cont.weaken Ct.weaken := by
  induction h
  case empty => simp [CaptureSet.weaken]; constructor
  case union ih1 ih2 =>
    simp [CaptureSet.weaken] at *
    apply union <;> aesop
  case singleton hb _ ih =>
    apply singleton
    { simp [FinFun.weaken]
      have hb1 := Context.Bound.there_label (S:=S) hb
      simp [CaptureSet.weaken, CaptureSet.rename] at hb1
      exact hb1 }
    { exact ih }
  case csingleton hb _ ih =>
    apply csingleton
    { have hb1 := Context.CBound.there_label (S:=S) hb
      exact hb1 }
    { exact ih }
  case label hb hs =>
    apply label
    { have hb1 := Context.LBound.there_label (S':=S) hb
      exact hb1 }
    { apply hs.lweaken }

theorem TypedCont.lweaken
  (h : TypedCont Γ E cont E' Ct) :
  TypedCont (Γ.label S) E.weaken cont.weaken E'.weaken Ct.weaken := by
  induction h
  case none =>
    simp [Cont.weaken]
    apply none
    apply? ESubtyp.lweaken
  case cons ih =>
    simp [Cont.weaken]
    have heq : ∀ {n m k} {T0 : CType n m k}, (EType.type T0).weaken = EType.type T0.weaken := by
      intro T0
      simp [EType.weaken, EType.rename, CType.weaken]
    rw [heq]
    apply cons
    { rename_i ht _ _
      have ht1 := ht.lweaken_ext (P := S)
      rw [EType.weaken1_weaken] at ht1
      rw [CaptureSet.weaken1_weaken] at ht1
      exact ht1 }
    { apply WellScoped.lweaken; assumption }
    { exact ih }
  case conse ih =>
    simp [Cont.weaken, EType.weaken_ex]
    apply conse
    { rename_i ht _ _
      have ht1 := ht.lweaken_cext_ext (P := S)
      rw [EType.weaken1_weaken] at ht1
      rw [EType.weaken_cweaken] at ht1
      rw [CaptureSet.weaken1_weaken] at ht1
      rw [CaptureSet.weaken_cweaken] at ht1
      exact ht1 }
    { apply WellScoped.lweaken; aesop }
    { exact ih }
  case scope hs ih =>
    simp [Cont.weaken]
    apply scope
    { constructor; aesop }
    { aesop }
    { apply hs.lweaken }

end Capless
