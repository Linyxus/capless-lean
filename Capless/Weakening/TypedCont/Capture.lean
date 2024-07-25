import Capless.Store
namespace Capless

theorem TypedCont.cweaken
  (h : TypedCont Γ E t E') :
  TypedCont (Γ.cvar b) E.cweaken t.cweaken E'.cweaken := sorry

end Capless
