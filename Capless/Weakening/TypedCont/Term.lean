import Capless.Store
import Capless.Weakening.Typing
namespace Capless

theorem EType.weaken1_weaken (E : EType n m k) :
  E.weaken.weaken1 = E.weaken.weaken := by
  simp [EType.weaken, EType.weaken1, EType.rename_rename]
  rw [<- FinFun.comp_weaken]

theorem EType.weaken_ex (T : CType n m (k+1)) :
  (EType.ex T).weaken = EType.ex T.weaken := by
  simp [EType.weaken, EType.rename, CType.weaken]

theorem EType.weaken_cweaken (E : EType n m k) :
  E.cweaken.weaken = E.weaken.cweaken := by
  simp [EType.weaken, EType.cweaken, EType.crename_rename_comm]

theorem TypedCont.weaken
  (h : TypedCont Γ E t E') :
  TypedCont (Γ.var T) E.weaken t.weaken E'.weaken := by
  induction h
  case none =>
    simp [Cont.weaken]
    apply none
  case cons ih =>
    simp [Cont.weaken]
    have heq : ∀ {n m k} {T0 : CType n m k}, (EType.type T0).weaken = EType.type T0.weaken := by
      intro T0
      simp [EType.weaken, EType.rename, CType.weaken]
    rw [heq]
    apply cons
    { rename_i ht _
      have ht1 := ht.weaken_ext (P := T)
      rw [EType.weaken1_weaken] at ht1
      exact ht1 }
    { exact ih }
  case conse ih =>
    simp [Cont.weaken, EType.weaken_ex]
    apply conse
    { rename_i ht _
      have ht1 := ht.weaken_cext_ext (P := T)
      rw [EType.weaken1_weaken] at ht1
      rw [EType.weaken_cweaken] at ht1
      exact ht1 }
    { exact ih }

end Capless
