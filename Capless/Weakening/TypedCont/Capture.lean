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

theorem EType.cweaken1_cweaken (E : EType n m k) :
  E.cweaken.cweaken1 = E.cweaken.cweaken := by
  simp [EType.cweaken1, EType.cweaken, EType.crename_crename]
  simp [FinFun.comp_weaken]

theorem TypedCont.cweaken
  (h : TypedCont Γ E t E') :
  TypedCont (Γ.cvar b) E.cweaken t.cweaken E'.cweaken := by
  induction h
  case none =>
    simp [Cont.cweaken]
    apply none
    apply? ESubtyp.cweaken
  case cons ht _ ih =>
    simp [Cont.cweaken, EType.cweaken_type]
    apply cons
    { have ht1 := ht.cweaken_ext (b := b)
      rw [EType.cweaken_weaken] at ht1
      exact ht1 }
    { exact ih }
  case conse ht _ ih =>
    simp [Cont.cweaken, EType.cweaken_ex]
    apply conse
    { have ht1 := ht.cweaken_cext_ext (b := b)
      rw [EType.cweaken1_weaken] at ht1
      rw [EType.cweaken1_cweaken] at ht1
      exact ht1 }
    { exact ih }

end Capless
