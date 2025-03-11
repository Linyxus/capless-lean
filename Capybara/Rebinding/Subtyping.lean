import Capybara.StaticSemantics
import Capybara.Rebinding.Subcapturing
namespace Capybara

private def motive_1
  (Γ : Context n m k) (S1 S2 : SType n m k)
  (_ : SSubtyping Γ S1 S2) : Prop :=
  ∀ {n' m' k'} {Δ : Context n' m' k'} (θ : Rebinding Γ Δ), SSubtyping Δ (S1.rename θ.ρ) (S2.rename θ.ρ)

private def motive_2
  (Γ : Context n m k) (T1 T2 : CType n m k)
  (_ : CSubtyping Γ T1 T2) : Prop :=
  ∀ {n' m' k'} {Δ : Context n' m' k'} (θ : Rebinding Γ Δ), CSubtyping Δ (T1.rename θ.ρ) (T2.rename θ.ρ)

private def motive_3
  (Γ : Context n m k) (E1 E2 : EType n m k)
  (_ : ESubtyping Γ E1 E2) : Prop :=
  ∀ {n' m' k'} {Δ : Context n' m' k'} (θ : Rebinding Γ Δ), ESubtyping Δ (E1.rename θ.ρ) (E2.rename θ.ρ)

syntax "unfold_all" : tactic

macro_rules
  | `(tactic| unfold_all) => `(tactic| try unfold motive_1 at *; try unfold motive_2 at *; try unfold motive_3 at *)

theorem SSubtyping.rebind
  (h : SSubtyping Γ S1 S2)
  (θ : Rebinding Γ Δ) :
  SSubtyping Δ (S1.rename θ.ρ) (S2.rename θ.ρ) := by
  apply SSubtyping.rec
    (motive_1:=motive_1)
    (motive_2:=motive_2)
    (motive_3:=motive_3)
    (t:=h)
  all_goals (unfold_all; repeat intro)
  case top => constructor
  case refl => apply SSubtyping.refl
  case trans =>
    rename_i ih1 ih2 _ _ _ _ _
    apply trans <;> aesop
  case tvar =>
    rename_i hb _ _ _ _ θ
    apply tvar
    have hb1 := θ.tvar hb
    exact hb1
  case arrow T2 T1 _ _ _ _ ih1 ih2 _ _ _ _ θ =>
    simp [SType.rename]
    apply arrow
    { aesop }
    { let θ' := θ.ext (T:=T2)
      apply ih2 θ' }
  case tarrow S2 S1 _ _ _ _ ih1 ih2 _ _ _ _ θ =>
    unfold motive_3 at ih2
    simp [SType.rename]
    apply tarrow
    { aesop }
    { let θ' := θ.text (B:=tparam S2)
      apply ih2 θ' }
  case carrow K _ _ _ ih _ _ _ _ θ =>
    unfold motive_3 at ih
    simp [SType.rename]
    apply carrow
    { let θ' := θ.cext (K:=cparam (CKind.Sep K))
      apply ih θ' }
  case talias_l hb _ _ _ _ θ =>
    simp [SType.rename]
    apply talias_l
    have hb1 := θ.tvar hb
    exact hb1
  case talias_r hb _ _ _ _ θ =>
    simp [SType.rename]
    apply talias_r
    have hb1 := θ.tvar hb
    exact hb1
  case capt ih _ _ _ _ θ =>
    simp [CType.rename]
    apply CSubtyping.capt
    { aesop }
    { apply Subcapturing.rebind; easy }
  case type ih _ _ _ _ θ =>
    simp [EType.rename]
    apply ESubtyping.type
    { aesop }
  case ex ih _ _ _ _ θ =>
    unfold motive_2 at ih
    simp [EType.rename]
    apply ESubtyping.ex
    let θ' := θ.cext (K:=cparam CKind.Fresh)
    apply ih θ'

theorem CSubtyping.rebind
  (h : CSubtyping Γ T1 T2)
  (θ : Rebinding Γ Δ) :
  CSubtyping Δ (T1.rename θ.ρ) (T2.rename θ.ρ) := by
  cases h
  case capt hs hc =>
    simp [CType.rename]
    apply CSubtyping.capt
    { apply SSubtyping.rebind; easy }
    { apply Subcapturing.rebind; easy }

theorem ESubtyping.rebind
  (h : ESubtyping Γ E1 E2)
  (θ : Rebinding Γ Δ) :
  ESubtyping Δ (E1.rename θ.ρ) (E2.rename θ.ρ) := by
  cases h
  case type hc =>
    simp [EType.rename]
    apply ESubtyping.type
    apply CSubtyping.rebind; easy
  case ex hc =>
    simp [EType.rename]
    apply ESubtyping.ex
    let θ' := θ.cext (K:=cparam CKind.Fresh)
    apply CSubtyping.rebind hc θ'

end Capybara
