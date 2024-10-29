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

theorem CaptureSet.interp_weaken
  (hi : CaptureSet.Interp ρ Γ C D I) :
  CaptureSet.Interp ρ.ext (Γ.var P) C.weaken D.cweaken.weaken I.cweaken.weaken := by
  induction hi
  case i_empty =>
    simp [CaptureSet.weaken, CaptureSet.rename]
    simp [Capless.CaptureSet.weaken, Capless.CaptureSet.rename]
    constructor
  case i_union ih1 ih2 =>
    rw [CaptureSet.weaken_union]
    rw [Capless.CaptureSet.cweaken_union, Capless.CaptureSet.weaken_union]
    constructor <;> assumption
  case i_singleton hb hi0 ih =>
    simp [CaptureSet.weaken, CaptureSet.rename, Capless.FinFun.weaken]
    have hb1 := Context.Bound.there_var (T' := P) hb
    constructor
    exact hb1
    rw [TMap.ext_reach_succ]
    rw [Capless.CaptureSet.cweaken_csingleton] at ih
    rw [Capless.CaptureSet.weaken_csingleton] at ih
    exact ih
  case i_reach =>
    simp [CaptureSet.weaken, CaptureSet.rename]
    constructor
  case i_cap =>
    simp [CaptureSet.weaken, CaptureSet.rename]
    constructor

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

theorem CaptureSet.interp_complete'
  (hl : CaptureSet.Lift C C') :
  ∃ I, CaptureSet.Interp ρ Γ C' D I := by
  rename_i n n' m k
  induction n generalizing n' m k
  case zero =>
    induction C generalizing C' D
    case empty =>
      have h := CaptureSet.lift_empty hl
      cases h
      constructor; constructor
    case union ih1 ih2 =>
      have ⟨D1, D2, hl1, hl2, he⟩ := CaptureSet.lift_union hl
      have ⟨I1, hi1⟩ := ih1 (D := D) hl1
      have ⟨I2, hi2⟩ := ih2 (D := D) hl2
      rw [he]
      constructor; constructor <;> assumption
    case singleton => sorry
    case reach => sorry
    case universal => sorry
  case succ => sorry

theorem CaptureSet.interp_complete :
  ∃ I, CaptureSet.Interp ρ Γ C D I := by
  rename_i n m k
  induction n generalizing m k
  case zero =>
    induction C generalizing D
    case empty => constructor; constructor
    case union ih1 ih2 =>
      have ⟨I1, ih1⟩ := ih1 (D := D)
      have ⟨I2, ih2⟩ := ih2 (D := D)
      constructor; constructor <;> assumption
    case singleton x0 => apply Fin.elim0; assumption
    case reach => constructor; constructor
    case universal => constructor; constructor
  case succ n0 ih =>
    induction C generalizing D
    case empty => constructor; constructor
    case union ih1 ih2 =>
      have ⟨I1, ih1⟩ := ih1 (D := D)
      have ⟨I2, ih2⟩ := ih2 (D := D)
      constructor; constructor <;> assumption
    case singleton x0 =>
      cases x0 using Fin.cases
      case zero =>
        cases Γ; rename_i Γ0 P
        cases P; rename_i C S
        have hb0 := Context.Bound.here (Γ := Γ0) (T := (S^C))
        rw [CType.weaken_capt] at hb0
        constructor
        constructor
        { exact hb0 }
        { sorry }
        all_goals sorry
      case succ x0 => sorry
    case reach => constructor; constructor
    case universal => constructor; constructor

end Cappy
