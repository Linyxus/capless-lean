import Cappy.Translation.Encoding.CaptureSet.Core
namespace Cappy

theorem CaptureSet.interp_inj
  (hi1 : CaptureSet.Interp ρ Γ C D I1)
  (hi2 : CaptureSet.Interp ρ Γ C D I2) :
  I1 = I2 := by
  induction hi1 generalizing I2 <;> try (solve | cases hi2; trivial)
  case i_union ih1 ih2 =>
    cases hi2
    aesop
  case i_singleton hb1 _ ih =>
    cases hi2; rename_i hb2 _
    have h := Context.bound_inj hb1 hb2
    aesop

theorem CaptureSet.weaken_union {C1 C2 : CaptureSet n} :
  (C1 ∪ C2).weaken = C1.weaken ∪ C2.weaken := by
  simp [CaptureSet.weaken, CaptureSet.rename]

theorem CType.weaken_capt :
  (S^C : CType n m).weaken = S.weaken^C.weaken := by
  simp [CType.weaken, CType.rename, CaptureSet.weaken, SType.weaken, RenameFun.weaken]

theorem CType.tweaken_capt :
  (S^C : CType n m).tweaken = S.tweaken^C := by
  simp [CType.tweaken, CType.rename, SType.tweaken, RenameFun.tweaken]
  simp [CaptureSet.rename_id]

theorem Capless.CaptureSet.weaken_union {C1 C2 : Capless.CaptureSet n k} :
  (C1 ∪ C2).weaken = C1.weaken ∪ C2.weaken := by
  simp [Capless.CaptureSet.weaken, Capless.CaptureSet.rename]

theorem Capless.CaptureSet.cweaken_union {C1 C2 : Capless.CaptureSet n k} :
  (C1 ∪ C2).cweaken = C1.cweaken ∪ C2.cweaken := by
  simp [Capless.CaptureSet.cweaken, Capless.CaptureSet.crename]

theorem Capless.CaptureSet.weaken_csingleton :
  ({c=x} : Capless.CaptureSet n k).weaken = {c=x} := by
  simp [Capless.CaptureSet.weaken, Capless.CaptureSet.rename]

theorem TMap.ext_reach_succ {ρ : TMap n m k} :
  ρ.ext.reach x.succ = (ρ.reach x).succ := by
  simp [TMap.ext, Capless.FinFun.ext]

inductive CaptureSet.Lift : CaptureSet n -> CaptureSet n' -> Prop where
| refl : CaptureSet.Lift C C
| step :
  CaptureSet.Lift C C' ->
  CaptureSet.Lift C C'.weaken

theorem CaptureSet.lift_empty'
  (he : C0 = {})
  (hl : CaptureSet.Lift C0 C) : C = {} := by
  induction hl
  case refl => assumption
  case step hl => aesop

theorem CaptureSet.lift_empty
  (hl : CaptureSet.Lift ({} : CaptureSet n) C) : C = {} :=
  CaptureSet.lift_empty' rfl hl

theorem CaptureSet.lift_union'
  (he : C0 = C1 ∪ C2)
  (hl : CaptureSet.Lift C0 D) :
  ∃ D1 D2, CaptureSet.Lift C1 D1 ∧ CaptureSet.Lift C2 D2 ∧ D = D1 ∪ D2 := by
  induction hl
  case refl =>
    constructor; constructor
    constructor; constructor
    constructor; constructor
    assumption
  case step hl ih =>
    have ih := ih he
    have ⟨D1, D2, ih1, ih2, he⟩ := ih
    apply Exists.intro D1.weaken
    apply Exists.intro D2.weaken
    constructor
    constructor; assumption
    constructor
    constructor; assumption
    rw [he, CaptureSet.weaken_union]

theorem CaptureSet.lift_union
  (hl : CaptureSet.Lift (C1 ∪ C2) D) :
  ∃ D1 D2, CaptureSet.Lift C1 D1 ∧ CaptureSet.Lift C2 D2 ∧ D = D1 ∪ D2 := by
  apply CaptureSet.lift_union' rfl hl

theorem CaptureSet.lift_cap'
  (he : C0 = {cap})
  (hl : CaptureSet.Lift C0 D) :
  D = {cap} := by
  induction hl
  case refl => aesop
  case step ih =>
    have ih := ih he
    rw [ih]
    simp [CaptureSet.weaken, CaptureSet.rename]

theorem CaptureSet.lift_cap
  (hl : CaptureSet.Lift ({cap} : CaptureSet n) D) :
  D = {cap} :=
  CaptureSet.lift_cap' rfl hl

theorem CaptureSet.lift_reach'
  (he : C0 = {x*=x})
  (hl : CaptureSet.Lift C0 D) :
  ∃ y, D = {x*=y} := by
  induction hl
  case refl => aesop
  case step ih =>
    have ⟨y0, ih⟩ := ih he
    rw [ih]
    simp [CaptureSet.weaken, CaptureSet.rename]

theorem CaptureSet.lift_reach
  (hl : CaptureSet.Lift {x*=xC0} D) :
  ∃ y, D = {x*=y} :=
  CaptureSet.lift_reach' rfl hl

def CaptureSet.InterpComplete (Γ : Context n m) :=
  ∀ {k} (ρ : TMap n m k) C D, ∃ I, CaptureSet.Interp ρ Γ C D I

theorem CaptureSet.interp_weaken
  (hi : CaptureSet.Interp ρ Γ C D I) :
  ∃ I', CaptureSet.Interp ρ' (Γ.var P) C.weaken D' I' := by
  induction hi generalizing ρ' D'
  case i_empty =>
    simp [weaken, rename]
    constructor; constructor
  case i_union ih1 ih2 =>
    have ⟨I1, ih1⟩ := ih1 (ρ' := ρ') (D' := D')
    have ⟨I2, ih2⟩ := ih2 (ρ' := ρ') (D' := D')
    rw [CaptureSet.weaken_union]
    constructor; constructor <;> assumption
  case i_singleton x0 _ _ _ _ _ hb _ ih =>
    have hb1 := Context.Bound.there_var (T' := P) hb
    simp [CType.weaken_capt] at hb1
    simp [weaken, rename, Capless.FinFun.weaken]
    have ⟨I, ih⟩ := ih (ρ' := ρ') (D' := {c=ρ'.reach x0.succ})
    constructor; constructor
    { exact hb1 }
    { exact ih }
  case i_reach =>
    simp [weaken, rename, Capless.FinFun.weaken]
    constructor; constructor
  case i_cap =>
    simp [weaken, rename]
    constructor; constructor

theorem CaptureSet.interp_tweaken
  (hi : CaptureSet.Interp ρ Γ C D I) :
  ∃ I', CaptureSet.Interp ρ' (Γ.tvar S) C D' I' := by
  induction hi generalizing ρ' D'
  case i_empty => constructor; constructor
  case i_union ih1 ih2 =>
    have ⟨I1, ih1⟩ := ih1 (ρ' := ρ') (D' := D')
    have ⟨I2, ih2⟩ := ih2 (ρ' := ρ') (D' := D')
    constructor; constructor <;> assumption
  case i_singleton x0 _ _ _ _ _ hb0 _ ih =>
    have ⟨I0, hi0⟩ := ih (ρ' := ρ') (D' := {c=ρ'.reach x0})
    have hb := Context.Bound.there_tvar (S := S) hb0
    simp [CType.tweaken_capt] at hb
    constructor; constructor
    { exact hb }
    { exact hi0 }
  case i_reach => constructor; constructor
  case i_cap => constructor; constructor

theorem CaptureSet.interp_complete' :
  InterpComplete Γ := by
  induction Γ <;> (unfold InterpComplete; intro k ρ C D)
  case empty =>
    induction C
    case empty => constructor; constructor
    case union ih1 ih2 =>
      have ⟨I1, ih1⟩ := ih1
      have ⟨I2, ih2⟩ := ih2
      constructor; constructor <;> assumption
    case singleton x0 => apply Fin.elim0 x0
    case reach x0 => apply Fin.elim0 x0
    case universal => constructor; constructor
  case var Γ0 P0 ih =>
    induction C
    case empty => constructor; constructor
    case union ih1 ih2 =>
      have ⟨I1, ih1⟩ := ih1
      have ⟨I2, ih2⟩ := ih2
      constructor; constructor <;> assumption
    case singleton x0 =>
      cases P0; rename_i C0 S0
      have ⟨T0, hb0⟩ := Context.bound_exists (Γ:=Γ0.var (S0^C0)) (x:=x0)
      cases hb0
      case here =>
        have hb0 := Context.Bound.here (Γ := Γ0) (T := (S0^C0))
        simp [CType.weaken_capt] at hb0
        have ⟨I0, ih0⟩ := ih (ρ := ρ.strip) (C := C0) (D := {})
        have ⟨I1, ih1⟩ := CaptureSet.interp_weaken (ρ':=ρ) (D':={c=ρ.reach 0}) (P:=(S0^C0)) ih0
        constructor
        constructor
        { exact hb0 }
        { exact ih1 }
      case there_var x0 T0 hb0 =>
        have ⟨I0, ih0⟩ := ih (ρ := ρ.strip) (C:={x=x0}) (D:={})
        have ih1 := CaptureSet.interp_weaken (ρ':=ρ) (D':=D) (P:=(S0^C0)) ih0
        exact ih1
    case reach => constructor; constructor
    case universal => constructor; constructor
  case tvar Γ0 S0 ih =>
    have ⟨I0, h0⟩ := ih (ρ:=ρ.tstrip) (C:=C) (D:=D)
    have h1 := CaptureSet.interp_tweaken (ρ':=ρ) (D':=D) (S:=S0) h0
    exact h1

theorem CaptureSet.interp_complete :
  ∃ I, CaptureSet.Interp ρ Γ C D I :=
  CaptureSet.interp_complete' ρ C D

end Cappy
