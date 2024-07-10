import Capless.Typing
import Capless.Renaming.Basic
import Capless.Renaming.Type.Subtyping
namespace Capless

theorem SealedLet.neg_trename
  (h : ¬ SealedLet t C) :
  ¬ SealedLet (t.trename f) C := by
  intro h0
  apply h
  cases h0
  case mk hv hl =>
    constructor
    apply IsValue.trename_l; trivial
    trivial

theorem SealedLet.trename
  (h : SealedLet t C) :
  SealedLet (t.trename f) C := by
  cases h
  case mk hv hl =>
    constructor
    apply IsValue.trename_r; trivial
    trivial

theorem Captured.trename
  {f : FinFun m m'}
  (h : Captured t C) :
  Captured (t.trename f) C := by
  induction h generalizing m'
  case var => simp [Term.trename]; apply var
  case lam =>
    simp [Term.trename]
    apply lam
    aesop
    aesop
  case tlam =>
    simp [Term.trename]
    apply tlam
    aesop
  case clam =>
    simp [Term.trename]
    apply clam
    aesop
    aesop
  case boxed =>
    simp [Term.trename]
    apply boxed
  case pack =>
    simp [Term.trename]
    apply pack
  case app =>
    simp [Term.trename]
    apply app
  case tapp =>
    simp [Term.trename]
    apply tapp
  case capp =>
    simp [Term.trename]
    apply capp
  case unbox =>
    simp [Term.trename]
    apply unbox
  case letin =>
    simp [Term.trename]
    apply letin
    aesop
    aesop
    apply SealedLet.neg_trename; trivial
    trivial
  case letin_sealed =>
    simp [Term.trename]
    apply letin_sealed
    aesop
    aesop
    apply SealedLet.trename; trivial
  case letex =>
    simp [Term.trename]
    apply letex
    aesop
    aesop
    trivial

theorem Typed.trename
  {Γ : Context n m k} {Δ : Context n m' k}
  (h : Typed Γ t E)
  (ρ : TVarMap Γ f Δ) :
  Typed Δ (t.trename f) (E.trename f) := by
  induction h generalizing m'
  case var =>
    simp [Term.trename, EType.trename]
    apply var
    apply ρ.map; trivial
  -- case exists_elim ih =>
  --   simp [Term.trename, EType.trename, CType.trename]
  --   rw [SType.trename_copen]
  --   apply exists_elim
  --   have ih := ih ρ
  --   simp [Term.trename, EType.trename, CType.trename] at ih
  --   exact ih
  --   rename_i hb
  --   have hb1 := ρ.cmap _ _ hb
  --   exact hb1
  case pack ih =>
    simp [Term.trename, EType.trename]
    apply pack
    have ih := ih ρ
    simp [Term.trename, EType.trename] at ih
    rw [<- CType.trename_copen]
    trivial
  case sub hs ih =>
    apply sub
    aesop
    apply ESubtyp.trename <;> trivial
  case abs hcv ih =>
    simp [Term.trename, EType.trename, CType.trename, SType.trename]
    apply abs
    apply ih <;> try trivial
    apply TVarMap.ext; trivial
    have hcv1 := hcv.trename (f := f)
    simp [Term.trename] at hcv1
    trivial
  case app ih1 ih2 =>
    simp [Term.trename]
    rw [EType.trename_open]
    apply app
    have ih1 := ih1 ρ
    simp [EType.trename, CType.trename, SType.trename, Term.trename] at ih1
    trivial
    have ih2 := ih2 ρ
    simp [Term.trename, EType.trename] at ih2
    trivial
  case tabs hcv ih =>
    simp [Term.trename, EType.trename, CType.trename, SType.trename]
    apply tabs
    apply ih <;> try trivial
    apply TVarMap.text <;> trivial
    have hcv1 := hcv.trename (f := f)
    simp [Term.trename] at hcv1
    trivial
  case cabs hcv ih =>
    simp [Term.trename, EType.trename, CType.trename, SType.trename]
    apply cabs
    have ih1 := ih (ρ.cext _)
    trivial
    have hcv1 := hcv.trename (f := f)
    simp [Term.trename] at hcv1
    trivial
  case unbox ih =>
    simp [Term.trename, EType.trename, CType.trename]
    apply unbox
    have ih := ih ρ
    simp [Term.trename, EType.trename, CType.trename, SType.trename] at ih
    trivial
  case tapp ih =>
    simp [Term.trename]
    rw [EType.trename_topen]
    apply tapp
    have ih := ih ρ
    simp [Term.trename, EType.trename, CType.trename, SType.trename] at ih
    trivial
  case capp ih =>
    simp [Term.trename]
    rw [EType.trename_copen]
    apply capp
    have ih := ih ρ
    simp [Term.trename, EType.trename, CType.trename, SType.trename] at ih
    trivial
  case box ih =>
    simp [Term.trename, EType.trename, CType.trename, SType.trename]
    apply box
    have ih := ih ρ
    simp [Term.trename, EType.trename] at ih
    trivial
  case letin ih1 ih2 =>
    simp [Term.trename]
    apply letin
    simp [EType.trename] at ih1
    aesop
    have ih2 := ih2 (ρ.ext _)
    rw [<- EType.weaken_trename] at ih2
    trivial
  case letex ih1 ih2 =>
    simp [Term.trename]
    apply letex
    simp [EType.trename] at ih1
    aesop
    have ih2 := ih2 ((ρ.cext _).ext _)
    rw [<- EType.weaken_trename] at ih2
    rw [<- EType.cweaken_trename] at ih2
    trivial
  case bindt ih =>
    simp [Term.trename]
    apply bindt
    have ih := ih (ρ.text _)
    rw [EType.tweaken_trename]
    trivial
  case bindc ih =>
    simp [Term.trename]
    apply bindc
    have ih := ih (ρ.cext _)
    rw [EType.cweaken_trename]
    trivial

end Capless
