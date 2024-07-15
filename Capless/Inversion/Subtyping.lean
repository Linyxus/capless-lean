import Capless.Subtyping
import Capless.Store
import Capless.Inversion.Basic
namespace Capless

theorem ESubtyp.sub_type_inv'
  (he : E2 = EType.type T2)
  (h : ESubtyp Γ E1 E2) :
  ∃ T1, E1 = EType.type T1 ∧ CSubtyp Γ T1 T2 := by
  cases h <;> try (solve | cases he)
  case type T1 T2 hs =>
    cases he
    exists T1

theorem ESubtyp.sub_type_inv
  (h : ESubtyp Γ E1 (EType.type T2)) :
  ∃ T1, E1 = EType.type T1 ∧ CSubtyp Γ T1 T2 := by
  apply ESubtyp.sub_type_inv' rfl h

def SSubtyp.dealias_right_forall.emotive
  (Γ : Context n m k)
  (E1 : EType n m k)
  (E2 : EType n m k)
  : Prop := True

def SSubtyp.dealias_right_forall.cmotive
  (Γ : Context n m k)
  (C1 : CType n m k)
  (C2 : CType n m k)
  : Prop := True

def SSubtyp.dealias_right_forall.smotive
  (Γ : Context n m k)
  (S1 : SType n m k)
  (S2 : SType n m k)
  : Prop :=
  ∀ {T2 E2} (ht : Γ.IsTight) (hd : SType.Dealias Γ S2 (SType.forall T2 E2)),
    ∃ T1 E1, SType.Dealias Γ S1 (SType.forall T1 E1)

theorem SSubtyp.dealias_right_forall
  (h : SSubtyp Γ S1 S2) (ht : Γ.IsTight)
  (hd : SType.Dealias Γ S2 (SType.forall T2 E2)) :
  ∃ T1 E1, SType.Dealias Γ S1 (SType.forall T1 E1) := by
  apply SSubtyp.rec
    (motive_1 := fun Γ E1 E2 h => SSubtyp.dealias_right_forall.emotive Γ E1 E2)
    (motive_2 := fun Γ C1 C2 h => SSubtyp.dealias_right_forall.cmotive Γ C1 C2)
    (motive_3 := fun Γ S1 S2 h => SSubtyp.dealias_right_forall.smotive Γ S1 S2)
    (t := h) (hd := hd) (ht := ht)
  case exist =>
    unfold dealias_right_forall.cmotive dealias_right_forall.emotive
    aesop
  case type =>
    unfold dealias_right_forall.cmotive dealias_right_forall.emotive
    aesop
  case capt =>
    unfold dealias_right_forall.cmotive
    aesop
  case top =>
    unfold dealias_right_forall.smotive
    repeat intro
    rename_i hd
    cases hd
  case refl =>
    unfold dealias_right_forall.smotive
    repeat intro
    rename_i T2 E2 _ _
    exists T2, E2
  case trans =>
    unfold dealias_right_forall.smotive
    repeat intro
    rename_i ih1 ih2 T3 E3 ht3 hd3
    have ih2 := ih2 ht3 hd3
    have ⟨T2, E2, hd2⟩ := ih2
    have ih1 := ih1 ht3 hd2
    exact ih1
  case tvar =>
    unfold dealias_right_forall.smotive
    repeat intro
    rename_i hb _ _ ht _
    sorry
  case tinstl => sorry
  case tinstr => sorry
  case xforall => sorry
  case tforall => sorry
  case cforall => sorry
  case boxed => sorry

end Capless
