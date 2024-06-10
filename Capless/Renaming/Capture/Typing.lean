import Capless.Typing
import Capless.Renaming.Basic
import Capless.Renaming.Term.Subtyping
namespace Capless

theorem DropBinderFree.crename
  (h : DropBinderFree C1 C2) :
  DropBinderFree (C1.crename f) (C2.crename f) := by
  cases h
  rw [<- CaptureSet.weaken_crename]
  constructor

theorem DropBinder.crename
  (h : DropBinder C1 C2) :
  DropBinder (C1.crename f) (C2.crename f) := by
  cases h
  case drop_free =>
    constructor
    apply DropBinderFree.crename; trivial
  case drop =>
    simp [CaptureSet.crename_union]
    simp [CaptureSet.crename_singleton]
    rw [<- CaptureSet.weaken_crename]
    apply drop

theorem DropCBinder.crename
  (h : DropCBinder C1 C2) :
  DropCBinder (C1.crename f.ext) (C2.crename f) := by
  cases h
  rw [<- CaptureSet.cweaken_crename]
  constructor

end Capless
