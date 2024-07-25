import Capless.Store
namespace Capless

theorem TypedCont.tweaken
  (h : TypedCont Γ E t E') :
  TypedCont (Γ.tvar S) E.tweaken t.tweaken E'.tweaken := sorry


end Capless
