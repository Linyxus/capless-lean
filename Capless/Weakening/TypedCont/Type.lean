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

theorem TypedCont.tweaken
  (h : TypedCont Γ E t E') :
  TypedCont (Γ.tvar S) E.tweaken t.tweaken E'.tweaken := by
  induction h
  case none =>
    simp [Cont.tweaken]
    apply none
    apply? ESubtyp.tweaken
  case cons ht _ ih =>
    simp [Cont.tweaken]
    simp [EType.tweaken_type]
    apply cons
    { have ht1 := ht.tweaken_ext (b := S)
      rw [EType.tweaken_weaken] at ht1
      exact ht1 }
    { exact ih }
  case conse ht _ ih =>
    simp [Cont.tweaken]
    simp [EType.tweaken_ex]
    apply conse
    { have ht1 := ht.tweaken_cext_ext (b := S)
      rw [EType.tweaken_weaken] at ht1
      rw [EType.tweaken_cweaken] at ht1
      exact ht1 }
    { exact ih }

end Capless
