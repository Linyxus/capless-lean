import Capless.Subtyping
import Capless.Store
import Capless.Inversion.Basic
import Capless.Inversion.Context
import Capless.Subtyping.Basic
import Capless.Subst.Term.Subtyping
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
    exfalso
    apply Context.tight_bound_tvar_absurd ht hb
  case tinstl =>
    unfold dealias_right_forall.smotive
    repeat intro
    rename_i hd
    cases hd
    case step hb0 hd0 =>
      rename_i hb1 _ _ _ _
      have h := Context.tbound_inj hb0 hb1
      cases h
      aesop
  case tinstr =>
    unfold dealias_right_forall.smotive
    repeat intro
    constructor; constructor
    apply SType.Dealias.step
    { trivial }
    { trivial }
  case xforall =>
    unfold dealias_right_forall.emotive dealias_right_forall.cmotive dealias_right_forall.smotive
    repeat intro
    constructor; constructor
    apply SType.Dealias.refl
  case tforall =>
    unfold dealias_right_forall.smotive dealias_right_forall.emotive
    repeat intro
    rename_i hd
    cases hd
  case cforall =>
    unfold dealias_right_forall.smotive dealias_right_forall.emotive
    repeat intro
    rename_i hd
    cases hd
  case boxed =>
    unfold dealias_right_forall.cmotive
    repeat intro
    rename_i hd
    cases hd


def SSubtyp.dealias_right_tforall.emotive
  (Γ : Context n m k)
  (E1 : EType n m k)
  (E2 : EType n m k)
  : Prop := True

def SSubtyp.dealias_right_tforall.cmotive
  (Γ : Context n m k)
  (C1 : CType n m k)
  (C2 : CType n m k)
  : Prop := True

def SSubtyp.dealias_right_tforall.smotive
  (Γ : Context n m k)
  (S1 : SType n m k)
  (S2 : SType n m k)
  : Prop :=
  ∀ {T2 E2} (ht : Γ.IsTight) (hd : SType.Dealias Γ S2 (SType.tforall T2 E2)),
    ∃ T1 E1, SType.Dealias Γ S1 (SType.tforall T1 E1)

theorem SSubtyp.dealias_right_tforall
  (h : SSubtyp Γ S1 S2) (ht : Γ.IsTight)
  (hd : SType.Dealias Γ S2 (SType.tforall T2 E2)) :
  ∃ T1 E1, SType.Dealias Γ S1 (SType.tforall T1 E1) := by
  apply SSubtyp.rec
    (motive_1 := fun Γ E1 E2 h => SSubtyp.dealias_right_tforall.emotive Γ E1 E2)
    (motive_2 := fun Γ C1 C2 h => SSubtyp.dealias_right_tforall.cmotive Γ C1 C2)
    (motive_3 := fun Γ S1 S2 h => SSubtyp.dealias_right_tforall.smotive Γ S1 S2)
    (t := h) (hd := hd) (ht := ht)
  case exist => aesop
  case type => aesop
  case capt =>
    unfold dealias_right_tforall.cmotive
    aesop
  case top =>
    unfold dealias_right_tforall.smotive
    repeat intro
    rename_i hd
    cases hd
  case refl =>
    unfold dealias_right_tforall.smotive
    repeat intro
    rename_i T2 E2 _ _
    exists T2, E2
  case trans =>
    unfold dealias_right_tforall.smotive
    repeat intro
    rename_i ih1 ih2 T3 E3 ht3 hd3
    have ih2 := ih2 ht3 hd3
    have ⟨T2, E2, hd2⟩ := ih2
    have ih1 := ih1 ht3 hd2
    exact ih1
  case tvar =>
    unfold dealias_right_tforall.smotive
    repeat intro
    rename_i hb _ _ ht _
    exfalso
    apply Context.tight_bound_tvar_absurd ht hb
  case tinstl =>
    unfold dealias_right_tforall.smotive
    repeat intro
    rename_i hd
    cases hd
    case step hb0 hd0 =>
      rename_i hb1 _ _ _ _
      have h := Context.tbound_inj hb0 hb1
      cases h
      aesop
  case tinstr =>
    unfold dealias_right_tforall.smotive
    repeat intro
    constructor; constructor
    apply SType.Dealias.step
    { trivial }
    { trivial }
  case boxed =>
    unfold dealias_right_tforall.cmotive
    repeat intro
    rename_i hd
    cases hd
  case xforall =>
    unfold dealias_right_tforall.emotive dealias_right_tforall.cmotive dealias_right_tforall.smotive
    repeat intro
    rename_i hd
    cases hd
  case tforall =>
    unfold dealias_right_tforall.emotive dealias_right_tforall.smotive
    repeat intro
    rename_i hd
    repeat (apply Exists.intro)
    apply SType.Dealias.refl
  case cforall =>
    unfold dealias_right_tforall.emotive dealias_right_tforall.smotive
    repeat intro
    rename_i hd
    cases hd

theorem SType.dealias_forall_inj'
  (he1 : S1 = SType.forall T1 E1) (he2 : S2 = SType.forall T2 E2)
  (h1 : SType.Dealias Γ S S1)
  (h2 : SType.Dealias Γ S S2) :
  T1 = T2 ∧ E1 = E2 := by
  induction h1 generalizing T2 E2
  case refl =>
    subst he1
    cases h2
    aesop
  case step hb1 hd1 ih =>
    cases h2
    case refl => cases he2
    case step hb2 hd2 =>
      apply ih
      { trivial }
      { trivial }
      { have h := Context.tbound_inj hb1 hb2
        cases h
        trivial }

theorem SType.dealias_forall_inj
  (h1 : SType.Dealias Γ S (SType.forall T1 E1))
  (h2 : SType.Dealias Γ S (SType.forall T2 E2)) :
  T1 = T2 ∧ E1 = E2 :=
  SType.dealias_forall_inj' rfl rfl h1 h2

theorem SType.dealias_tforall_inj'
  (he1 : S1 = SType.tforall T1 E1) (he2 : S2 = SType.tforall T2 E2)
  (h1 : SType.Dealias Γ S S1)
  (h2 : SType.Dealias Γ S S2) :
  T1 = T2 ∧ E1 = E2 := by
  induction h1 generalizing T2 E2
  case refl =>
    subst he1
    cases h2
    aesop
  case step hb1 hd1 ih =>
    cases h2
    case refl => cases he2
    case step hb2 hd2 =>
      apply ih
      { trivial }
      { trivial }
      { have h := Context.tbound_inj hb1 hb2
        cases h
        trivial }

theorem SType.dealias_tforall_inj
  (h1 : SType.Dealias Γ S (SType.tforall T1 E1))
  (h2 : SType.Dealias Γ S (SType.tforall T2 E2)) :
  T1 = T2 ∧ E1 = E2 :=
  SType.dealias_tforall_inj' rfl rfl h1 h2

def SSubtyp.dealias_forall_inv.emotive
  (Γ : Context n m k)
  (E1 : EType n m k)
  (E2 : EType n m k)
  : Prop := True

def SSubtyp.dealias_forall_inv.cmotive
  (Γ : Context n m k)
  (C1 : CType n m k)
  (C2 : CType n m k)
  : Prop := True

def SSubtyp.dealias_forall_inv.smotive
  (Γ : Context n m k)
  (S1 : SType n m k)
  (S2 : SType n m k)
  : Prop :=
  ∀ {T1 E1 T2 E2}
    (ht : Γ.IsTight)
    (h1 : SType.Dealias Γ S1 (SType.forall T1 E1))
    (h2 : SType.Dealias Γ S2 (SType.forall T2 E2)),
    CSubtyp Γ T2 T1 ∧ ESubtyp (Γ.var T2) E1 E2

theorem SSubtyp.sub_dealias_forall_inv
  (ht : Γ.IsTight)
  (h1 : SType.Dealias Γ S1 (SType.forall T1 E1))
  (h2 : SType.Dealias Γ S2 (SType.forall T2 E2))
  (hs : SSubtyp Γ S1 S2) :
  CSubtyp Γ T2 T1 ∧ ESubtyp (Γ.var T2) E1 E2 := by
  apply SSubtyp.rec
    (motive_1 := fun Γ E1 E2 h => SSubtyp.dealias_forall_inv.emotive Γ E1 E2)
    (motive_2 := fun Γ C1 C2 h => SSubtyp.dealias_forall_inv.cmotive Γ C1 C2)
    (motive_3 := fun Γ S1 S2 h => SSubtyp.dealias_forall_inv.smotive Γ S1 S2)
    (t := hs) (h1 := h1) (h2 := h2) (ht := ht)
  case exist => aesop
  case type => aesop
  case capt => unfold dealias_forall_inv.cmotive; aesop
  case top =>
    unfold dealias_forall_inv.smotive
    repeat intro
    rename_i hd2
    cases hd2
  case refl =>
    unfold dealias_forall_inv.smotive
    repeat intro
    rename_i hd1 hd2
    have h := SType.dealias_forall_inj hd1 hd2
    cases h; subst_vars
    constructor
    { apply CSubtyp.refl }
    { apply ESubtyp.refl }
  case xforall =>
    unfold dealias_forall_inv.emotive dealias_forall_inv.cmotive dealias_forall_inv.smotive
    repeat intro
    rename_i hd1 hd2
    cases hd1; cases hd2
    aesop
  case trans =>
    unfold dealias_forall_inv.smotive
    repeat intro
    rename_i hs1 hs2 ih1 ih2 T1 E1 T2 E2 ht hd1 hd2
    have h := SSubtyp.dealias_right_forall hs2 ht hd2
    have ⟨T3, E3, hd3⟩ := h
    have ⟨hc1, he1⟩ := ih1 ht hd1 hd3
    have ⟨hc2, he2⟩ := ih2 ht hd3 hd2
    have he1' := he1.narrow hc2
    constructor
    { apply CSubtyp.trans <;> trivial }
    { apply ESubtyp.trans <;> trivial }
  case tinstl =>
    unfold dealias_forall_inv.smotive
    repeat intro
    rename_i hd
    cases hd
    rename_i hb1 _ _ _ _ _ _ _ hb2 _
    have h := Context.tbound_inj hb1 hb2
    cases h
    rename_i hd1 hd2
    have h := SType.dealias_forall_inj hd1 hd2
    cases h
    subst_vars
    constructor
    { apply CSubtyp.refl }
    { apply ESubtyp.refl }
  case tinstr =>
    unfold dealias_forall_inv.smotive
    repeat intro
    rename_i hd _
    cases hd
    rename_i hb1 _ _ _ _ _ _ _ hb2 _
    have h := Context.tbound_inj hb1 hb2
    cases h
    rename_i hd1 hd2
    have h := SType.dealias_forall_inj hd1 hd2
    cases h
    subst_vars
    constructor
    { apply CSubtyp.refl }
    { apply ESubtyp.refl }
  case tvar =>
    unfold dealias_forall_inv.smotive
    repeat intro
    rename_i hd _
    cases hd
    rename_i hb1 _ _ _ _ _ _ _ hb2 _
    have h := Context.tbound_inj hb1 hb2
    cases h
  case boxed =>
    unfold dealias_forall_inv.cmotive dealias_forall_inv.smotive
    repeat intro
    rename_i hd
    cases hd
  case tforall =>
    unfold dealias_forall_inv.smotive
    repeat intro
    rename_i hd
    cases hd
  case cforall =>
    unfold dealias_forall_inv.smotive
    repeat intro
    rename_i hd
    cases hd

def SSubtyp.dealias_tforall_inv.emotive
  (Γ : Context n m k)
  (E1 : EType n m k)
  (E2 : EType n m k)
  : Prop := True

def SSubtyp.dealias_tforall_inv.cmotive
  (Γ : Context n m k)
  (C1 : CType n m k)
  (C2 : CType n m k)
  : Prop := True

def SSubtyp.dealias_tforall_inv.smotive
  (Γ : Context n m k)
  (S1 : SType n m k)
  (S2 : SType n m k)
  : Prop :=
  ∀ {T1 E1 T2 E2}
    (ht : Γ.IsTight)
    (h1 : SType.Dealias Γ S1 (SType.tforall T1 E1))
    (h2 : SType.Dealias Γ S2 (SType.tforall T2 E2)),
    SSubtyp Γ T2 T1 ∧ ESubtyp (Γ.tvar (TBinding.bound T2)) E1 E2

theorem SSubtyp.sub_dealias_tforall_inv
  (ht : Γ.IsTight)
  (h1 : SType.Dealias Γ S1 (SType.tforall T1 E1))
  (h2 : SType.Dealias Γ S2 (SType.tforall T2 E2))
  (hs : SSubtyp Γ S1 S2) :
  SSubtyp Γ T2 T1 ∧ ESubtyp (Γ.tvar (TBinding.bound T2)) E1 E2 := by
  apply SSubtyp.rec
    (motive_1 := fun Γ E1 E2 h => SSubtyp.dealias_tforall_inv.emotive Γ E1 E2)
    (motive_2 := fun Γ C1 C2 h => SSubtyp.dealias_tforall_inv.cmotive Γ C1 C2)
    (motive_3 := fun Γ S1 S2 h => SSubtyp.dealias_tforall_inv.smotive Γ S1 S2)
    (t := hs) (h1 := h1) (h2 := h2) (ht := ht)
  case exist => aesop
  case type => aesop
  case capt => unfold dealias_tforall_inv.cmotive; aesop
  case top =>
    unfold dealias_tforall_inv.smotive
    repeat intro
    rename_i hd2
    cases hd2
  case refl =>
    unfold dealias_tforall_inv.smotive
    repeat intro
    rename_i hd1 hd2
    have h := SType.dealias_tforall_inj hd1 hd2
    cases h; subst_vars
    constructor
    { apply SSubtyp.refl }
    { apply ESubtyp.refl }
  case trans =>
    unfold dealias_tforall_inv.smotive
    repeat intro
    rename_i hs1 hs2 ih1 ih2 T1 E1 T2 E2 ht hd1 hd2
    have h := SSubtyp.dealias_right_tforall hs2 ht hd2
    have ⟨T3, E3, hd3⟩ := h
    have ⟨hs1, he1⟩ := ih1 ht hd1 hd3
    have ⟨hs2, he2⟩ := ih2 ht hd3 hd2
    sorry
  all_goals sorry

end Capless
