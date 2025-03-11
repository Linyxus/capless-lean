import Capybara.StaticSemantics
import Capybara.Rebinding.Subtyping
namespace Capybara

theorem Typed.rebind {Γ : Context n m k} {Δ : Context n' m' k'}
  (h : Typed C Γ t E)
  (θ : Rebinding Γ Δ) :
  Typed (C.rename θ.ρ.asCapt) Δ (t.rename θ.ρ) (E.rename θ.ρ) := by
  induction h generalizing n' m' k' Δ
  case var hb hp =>
    simp [CaptureSet.rename, Term.rename]
    simp [EType.rename, CType.rename, CaptureSet.rename]
    apply var
    have hb' := θ.var hb
    soeasy
  case pack hd hk ih =>
    simp [Term.rename, EType.rename]
    apply pack
    { have ih := ih θ
      simp [Term.rename, EType.rename] at ih
      simp [CType.copen_rename] at ih
      easy }
    { sorry }
    { sorry }
  case subc =>
    sorry
  case abs =>
    sorry
  case tabs =>
    sorry
  case cabs =>
    sorry
  case fabs =>
    sorry
  case app =>
    sorry
  case tapp =>
    sorry
  case capp =>
    sorry
  case fapp =>
    sorry
  case letin =>
    sorry
  case unpack =>
    sorry

end Capybara
