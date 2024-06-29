import Capless.Typing
import Capless.Renaming.Basic
import Capless.Renaming.Capture.Subtyping
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

theorem SealedLet.neg_crename
  (h : ¬ SealedLet t C2) :
  ¬ SealedLet (t.crename f) (C2.crename f) := by
  intro h0
  apply h
  cases h0
  case mk hv hl =>
    constructor
    apply IsValue.crename_l hv
    apply CaptureSet.nonlocal_crename_l rfl hl

theorem SealedLet.rename
  (h : SealedLet t C2) :
  SealedLet (t.crename f) (C2.crename f) := by
  cases h
  case mk hv hl =>
    constructor
    apply IsValue.crename_r hv
    apply CaptureSet.nonlocal_crename_r hl

theorem Captured.crename
  {f : FinFun k k'}
  (h : Captured t C) :
  Captured (t.crename f) (C.crename f) := by
  induction h generalizing k'
  case var =>
    simp [Term.crename, CaptureSet.crename_singleton]
    apply var
  case lam hc ih =>
    simp [Term.crename]
    apply lam
    apply ih
    apply DropBinder.crename hc
  case tlam ih =>
    simp [Term.crename]
    apply tlam
    apply ih
  case clam ih =>
    simp [Term.crename]
    apply clam
    apply ih
    apply DropCBinder.crename; trivial
  case boxed =>
    simp [Term.crename, CaptureSet.crename_empty]
    apply boxed
  case pack =>
    simp [Term.crename, CaptureSet.crename_singleton]
    apply pack
  case unpack =>
    simp [Term.crename, CaptureSet.crename_singleton]
    apply unpack
  case app =>
    simp [Term.crename, CaptureSet.crename_union, CaptureSet.crename_singleton]
    apply app
  case tapp =>
    simp [Term.crename, CaptureSet.crename_singleton]
    apply tapp
  case capp =>
    simp [Term.crename, CaptureSet.crename_singleton]
    apply capp
  case unbox =>
    simp [Term.crename, CaptureSet.crename_union, CaptureSet.crename_singleton]
    apply unbox
  case letin =>
    simp [Term.crename, CaptureSet.crename_union]
    apply letin
    aesop; aesop
    apply SealedLet.neg_crename; trivial
    apply DropBinder.crename; trivial
  case letin_sealed =>
    simp [Term.crename]
    apply letin_sealed; aesop; aesop
    rw [CaptureSet.weaken_crename]
    apply SealedLet.rename; trivial

theorem Typed.crename
  {Γ : Context n m k} {Δ : Context n m k'}
  (h : Typed Γ t E)
  (ρ : CVarMap Γ f Δ) :
  Typed Δ (t.crename f) (E.crename f) := by
  induction h generalizing k'
  case var =>
    simp [Term.crename]
    apply var
    apply ρ.map; trivial
  case unpack hb ih =>
    simp [Term.crename, EType.crename, CType.crename, CaptureSet.crename_singleton]
    rw [SType.crename_copen]
    apply unpack
    have ih := ih ρ
    simp [EType.crename, CType.crename] at ih
    exact ih
    have hb1 := ρ.cmap _ _ hb
    simp [CBinding.crename, CaptureSet.crename_rsingleton] at hb1
    exact hb1
  case pack ih =>
    simp [Term.crename, EType.crename]
    apply pack
    rw [<- CType.crename_copen]
    have ih := ih ρ
    simp [Term.crename, EType.crename] at ih
    exact ih
  case sub hsub ih =>
    apply sub
    apply ih ρ
    apply ESubtyp.crename hsub; trivial
  case abs hc ih =>
    simp [Term.crename, EType.crename, CType.crename, SType.crename]
    apply abs
    apply ih
    apply ρ.ext
    have hc1 := hc.crename (f := f)
    simp [Term.crename] at hc1; trivial
  case tabs hc ih =>
    simp [Term.crename, EType.crename, CType.crename, SType.crename]
    apply tabs
    apply ih
    apply ρ.text
    have hc1 := hc.crename (f := f)
    simp [Term.crename] at hc1; trivial
  case cabs hc ih =>
    simp [Term.crename, EType.crename, CType.crename, SType.crename]
    apply cabs
    apply ih
    apply ρ.cext
    have hc1 := hc.crename (f := f)
    simp [Term.crename] at hc1; trivial
  case app ih1 ih2 =>
    simp [Term.crename, EType.crename_open]
    apply app
    have ih1 := ih1 ρ
    simp [Term.crename, EType.crename, CType.crename, SType.crename] at ih1
    exact ih1
    have ih2 := ih2 ρ
    simp [Term.crename, EType.crename, CType.crename, SType.crename] at ih2
    exact ih2
  case tapp ih1 =>
    simp [Term.crename, EType.crename_topen]
    apply tapp
    have ih1 := ih1 ρ
    simp [Term.crename, EType.crename, CType.crename, SType.crename] at ih1
    exact ih1
  case capp ih1 =>
    simp [Term.crename, EType.crename_copen]
    apply capp
    have ih1 := ih1 ρ
    simp [Term.crename, EType.crename, CType.crename, SType.crename] at ih1
    exact ih1
  case box ih =>
    simp [Term.crename, EType.crename, CType.crename, SType.crename, CaptureSet.crename_empty]
    apply box
    have ih := ih ρ
    simp [Term.crename, EType.crename, CType.crename, SType.crename] at ih
    exact ih
  case unbox ih =>
    simp [Term.crename, EType.crename, CType.crename, SType.crename]
    apply unbox
    have ih := ih ρ
    simp [Term.crename, EType.crename, CType.crename, SType.crename] at ih
    exact ih
  case letin ih1 ih2 =>
    simp [Term.crename]
    apply letin
    have ih1 := ih1 ρ
    exact ih1
    have ih2 := ih2 (ρ.ext _)
    rw [<- EType.weaken_crename] at ih2
    exact ih2
  case bindt ih =>
    simp [Term.crename]
    apply bindt
    have ih := ih (ρ.text _)
    rw [<- EType.tweaken_crename] at ih
    exact ih
  case bindc ih =>
    simp [Term.crename]
    apply bindc
    have ih := ih (ρ.cext _)
    rw [<- EType.cweaken_crename] at ih
    exact ih

end Capless
