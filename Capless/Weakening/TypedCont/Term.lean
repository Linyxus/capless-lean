import Capless.Store
namespace Capless

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
      sorry }
    { exact ih }
  case conse ih => sorry

end Capless
