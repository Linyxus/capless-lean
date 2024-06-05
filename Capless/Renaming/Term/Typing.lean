import Capless.Typing
import Capless.Renaming.Basic
import Capless.Renaming.Term.Subtyping
namespace Capless

theorem DropBinderFree.rename
  (h : DropBinderFree C1 C2) :
  DropBinderFree (C1.rename f.ext) (C2.rename f) := by
  cases h
  rw [<- CaptureSet.weaken_rename]
  constructor

theorem DropBinder.rename
  (h : DropBinder C1 C2) :
  DropBinder (C1.rename f.ext) (C2.rename f) := by
  cases h
  case drop_free =>
    constructor; apply DropBinderFree.rename; assumption
  case drop =>
    simp [CaptureSet.rename_union]
    simp [CaptureSet.rename_singleton, FinFun.ext]
    rw [<- CaptureSet.weaken_rename]
    apply DropBinder.drop

theorem DropCBinder.rename
  (h : DropCBinder C1 C2) :
  DropCBinder (C1.rename f) (C2.rename f) := by
  cases h
  rw [CaptureSet.cweaken_rename_comm]
  constructor

theorem SealedLet.term_rename_l
  (h : SealedLet (t.rename f) C) :
  SealedLet t C := by
  cases h
  case mk hv _ =>
    constructor
    apply IsValue.rename_l hv
    trivial

theorem SealedLet.capture_rename_l'
  (he : C0 = C.rename (FinFun.ext f))
  (h : SealedLet t C0) :
  SealedLet t C := by
  cases h
  case mk hv hl =>
    constructor <;> try assumption
    apply CaptureSet.nonlocal_rename_l he hl

theorem SealedLet.capture_rename_l
  (h : SealedLet t (C.rename (FinFun.ext f))) :
  SealedLet t C := by
  apply SealedLet.capture_rename_l'
  rfl; assumption

theorem SealedLet.neg_rename
  (h : ¬SealedLet t C2) :
  ¬SealedLet (t.rename f) (C2.rename f.ext) := by
  intro h0
  apply h
  cases h0
  case mk hv hl =>
    constructor
    apply IsValue.rename_l hv
    apply CaptureSet.nonlocal_rename_l rfl hl

theorem SealedLet.rename
  (h : SealedLet t C) :
  SealedLet (t.rename f) (C.rename f.ext) := by
  cases h
  case mk hv hl =>
    constructor
    apply IsValue.rename_r hv
    apply CaptureSet.nonlocal_rename_r hl

theorem Captured.rename
  {f : FinFun n n'}
  (h : Captured t C) :
  Captured (t.rename f) (C.rename f) := by
  induction h generalizing n'
  case var =>
    simp [Term.rename, CaptureSet.rename_singleton]
    constructor
  case lam ih =>
    simp [Term.rename]
    constructor
    apply ih
    apply DropBinder.rename; assumption
  case tlam ih =>
    simp [Term.rename]
    constructor
    apply ih
  case clam ih =>
    simp [Term.rename]
    constructor
    apply ih
    apply DropCBinder.rename; assumption
  case boxed =>
    simp [Term.rename]
    constructor
  case pack =>
    simp [Term.rename]
    constructor
  case app =>
    simp [Term.rename, CaptureSet.rename_union, CaptureSet.rename_singleton]
    constructor
  case tapp =>
    simp [Term.rename, CaptureSet.rename_singleton]
    constructor
  case capp =>
    simp [Term.rename, CaptureSet.rename_singleton]
    constructor
  case letin ih1 ih2 =>
    simp [Term.rename, CaptureSet.rename_union]
    constructor
    apply ih1
    apply ih2
    apply SealedLet.neg_rename; assumption
    apply DropBinder.rename; assumption
  case letin_sealed ih1 ih2 =>
    simp [Term.rename]
    constructor
    apply ih1
    rw [CaptureSet.weaken_rename]
    apply ih2
    rw [CaptureSet.weaken_rename]
    apply SealedLet.rename; assumption
  case unbox =>
    simp [Term.rename, CaptureSet.rename_union]
    constructor

theorem Typing.rename
  {Γ : Context n m k} {Δ : Context n' m k}
  (h : Typed Γ t E)
  (ρ : VarMap Γ f Δ) :
  Typed Δ (t.rename f) (E.rename f) := by
  induction h generalizing n'
  case var hb =>
    simp [Term.rename]
    apply Typed.var
    apply ρ.map; trivial
  case exists_elim ih =>
    simp [EType.rename, CType.rename, CaptureSet.rename_singleton, SType.copen_rename_comm]
    simp [Term.rename]
    have ih := ih ρ
    simp [Term.rename, EType.rename, CType.rename] at ih
    apply Typed.exists_elim
    exact ih
    rename_i hbc _
    have hbc1 := ρ.cmap _ _ hbc
    simp [CaptureSet.rename_rsingleton] at hbc1
    trivial
  case pack ih =>
    simp [Term.rename, EType.rename]
    apply Typed.pack
    have ih := ih ρ
    simp [Term.rename, EType.rename] at ih
    rw [CType.copen_rename_comm] at ih
    exact ih
  case sub hs ih =>
    apply Typed.sub
    apply ih; trivial
    apply ESubtyp.rename <;> trivial
  case abs hcv iht =>
    simp [Term.rename, EType.rename, CType.rename, SType.rename]
    apply Typed.abs
    apply iht <;> try assumption
    apply ρ.ext
    have hcv1 := hcv.rename (f := f)
    simp [Term.rename] at hcv1
    trivial
  case tabs hcv iht =>
    simp [Term.rename, EType.rename, CType.rename, SType.rename]
    apply Typed.tabs
    apply iht <;> try assumption
    apply ρ.text
    have hcv1 := hcv.rename (f := f)
    simp [Term.rename] at hcv1
    trivial
  case cabs hcv iht =>
    simp [Term.rename, EType.rename, CType.rename, SType.rename]
    apply Typed.cabs
    apply iht <;> try assumption
    apply ρ.cext
    have hcv1 := hcv.rename (f := f)
    simp [Term.rename] at hcv1
    trivial
  case app ih1 ih2 =>
    simp [Term.rename]
    simp [EType.rename_open]
    apply Typed.app
    have ih1 := ih1 ρ
    simp [Term.rename, EType.rename, CType.rename, SType.rename] at ih1
    exact ih1
    have ih2 := ih2 ρ
    simp [Term.rename] at ih2
    exact ih2
  case tapp ih =>
    simp [Term.rename]
    simp [EType.rename_topen]
    apply Typed.tapp
    have ih := ih ρ
    simp [Term.rename, EType.rename, CType.rename, SType.rename] at ih
    trivial
  case capp ih =>
    simp [Term.rename, EType.rename_copen]
    apply Typed.capp
    have ih := ih ρ
    simp [Term.rename, EType.rename, CType.rename, SType.rename] at ih
    trivial
  case box ih =>
    simp [Term.rename, EType.rename, CType.rename, SType.rename]
    simp [CaptureSet.rename_empty]
    apply Typed.box
    have ih := ih ρ
    simp [Term.rename, EType.rename] at ih
    trivial
  case unbox ih =>
    simp [Term.rename, EType.rename, CType.rename]
    apply Typed.unbox
    have ih := ih ρ
    simp [Term.rename, EType.rename, CType.rename, CaptureSet.rename_empty] at ih
    simp [SType.rename, CType.rename] at ih
    trivial
  case letin ih1 ih2 =>
    simp [Term.rename]
    apply Typed.letin
    have ih1 := ih1 ρ
    exact ih1
    have ih2 := ih2 (ρ.ext _)
    rw [<- EType.weaken_rename] at ih2
    trivial
  case bindt ih =>
    simp [Term.rename]
    apply Typed.bindt
    have ih := ih (ρ.text _)
    simp [Term.rename, TBinding.rename, EType.rename, CType.rename] at ih
    rw [EType.tweaken_rename] at ih
    trivial
  case bindc ih =>
    simp [Term.rename]
    apply Typed.bindc
    have ih := ih (ρ.cext _)
    simp [Term.rename, CBinding.rename] at ih
    rw [EType.cweaken_rename_comm] at ih
    trivial

end Capless
