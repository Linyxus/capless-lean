import Capless.Store
import Capless.Weakening.Typing
import Capless.Weakening.Subtyping
namespace Capless

theorem EType.tweaken_ex (T : CType n m (k+1)) :
  (EType.ex T).tweaken = EType.ex T.tweaken := by
  simp [EType.tweaken, EType.trename, CType.tweaken]

theorem EType.tweaken_type (T : CType n m k) :
  (EType.type T).tweaken = EType.type T.tweaken := by
  simp [EType.tweaken, EType.trename, CType.tweaken]

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
    simp [EType.tweaken_type]
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
  case scope hb _ ih =>
    simp [Cont.tweaken]
    apply scope
    have hb1 := Context.LBound.there_tvar (b := S) hb
    exact hb1
    apply ih

end Capless
