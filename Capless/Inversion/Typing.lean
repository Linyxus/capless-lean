import Capless.Tactics
import Capless.Typing
import Capless.Subtyping.Basic
import Capless.Inversion.Subtyping
import Capless.Subst.Term.Typing
import Capless.Subst.Type.Typing
namespace Capless

theorem Typed.app_inv'
  (he : t0 = Term.app x y)
  (h : Typed Γ t0 E) :
  ∃ T Cf F E0, Typed Γ (Term.var x) (EType.type (CType.capt Cf (SType.forall T F)))
    ∧ Typed Γ (Term.var y) (EType.type T)
    ∧ E0 = F.open y
    ∧ ESubtyp Γ E0 E := by
    induction h <;> try (solve | cases he)
    case app x C T F y h1 h2 _ _ =>
      cases he
      exists T, C, F, (F.open y)
      repeat (constructor; trivial)
      apply ESubtyp.refl
    case sub hsub ih =>
      have ih := ih he
      have ⟨T0, Cf0, E0, F0, hx0, hy0, he0, hs0⟩ := ih
      exists T0, Cf0, E0, F0
      repeat (constructor; trivial)
      apply ESubtyp.trans
      { trivial }
      { trivial }

theorem Typed.app_inv
  (h : Typed Γ (Term.app x y) E) :
  ∃ T Cf F E0, Typed Γ (Term.var x) (EType.type (CType.capt Cf (SType.forall T F)))
    ∧ Typed Γ (Term.var y) (EType.type T)
    ∧ E0 = F.open y
    ∧ ESubtyp Γ E0 E :=
  Typed.app_inv' rfl h

theorem Typed.tapp_inv'
  (he : t0 = Term.tapp x X)
  (h : Typed Γ t0 E) :
  ∃ Cf F E0,
    Typed Γ (Term.var x) (EType.type (CType.capt Cf (SType.tforall (SType.tvar X) F)))
    ∧ E0 = F.topen X
    ∧ ESubtyp Γ E0 E := by
  induction h <;> try (solve | cases he)
  case tapp =>
    cases he
    repeat (apply Exists.intro)
    apply And.intro
    { trivial }
    apply And.intro
    { trivial }
    { apply ESubtyp.refl }
  case sub ht hs ih =>
    have ih := ih he
    have ⟨Cf, F, E0, hx, he0, hs0⟩ := ih
    have h := ESubtyp.trans hs0 hs
    aesop

theorem Typed.tapp_inv
  (h : Typed Γ (Term.tapp x X) E) :
  ∃ Cf F E0,
    Typed Γ (Term.var x) (EType.type (CType.capt Cf (SType.tforall (SType.tvar X) F)))
    ∧ E0 = F.topen X
    ∧ ESubtyp Γ E0 E :=
  Typed.tapp_inv' rfl h

theorem Typed.var_inv'
  (he1 : t0 = Term.var x)
  (he2 : E0 = EType.type T)
  (h : Typed Γ t0 E0) :
  ∃ T0, Γ.Bound x T0 ∧ CSubtyp Γ T0 T := by
  induction h <;> try (solve | cases he1 | cases he2)
  case var T0 hb =>
    cases he1; cases he2
    apply Exists.intro T0
    constructor
    { trivial }
    { apply CSubtyp.refl }
  case sub hs ih =>
    have h := ESubtyp.sub_type_inv' he2 hs
    have ⟨T1, he, hs1⟩ := h
    have ih := ih he1 he
    have ⟨T0, hb, hs0⟩ := ih
    apply Exists.intro T0
    constructor
    { trivial }
    { apply CSubtyp.trans <;> trivial }

theorem Typed.var_inv
  (h : Typed Γ (Term.var x) (EType.type T)) :
  ∃ T0, Γ.Bound x T0 ∧ CSubtyp Γ T0 T := by
  apply Typed.var_inv' rfl rfl h

theorem Typed.canonical_form_lam'
  (ht : Γ.IsTight)
  (he1 : t0 = Term.lam T t) (hd2 : SType.Dealias Γ S0 (SType.forall T' E))
  (he2 : E0 = EType.type (CType.capt Cf S0))
  (h : Typed Γ t0 E0) :
  CSubtyp Γ T' T ∧
  Typed (Γ.var T') t E := by
  induction h <;> try (solve | cases he1 | cases he2)
  case abs =>
    cases he1; cases he2
    cases hd2
    constructor
    { apply CSubtyp.refl }
    { aesop }
  case sub hs ih =>
    subst he2
    cases hs
    rename_i hs
    cases hs
    rename_i hsc hs
    have ⟨T1, E1, hd3⟩ := SSubtyp.dealias_right_forall hs ht hd2
    have ih := ih ht he1 hd3 rfl
    have h := SSubtyp.sub_dealias_forall_inv ht hd3 hd2 hs
    have ⟨hs1, ht1⟩ := ih
    have ⟨hs2, ht2⟩ := h
    apply And.intro
    { apply! CSubtyp.trans }
    { apply? Typed.sub
      apply! Typed.narrow }

theorem Typed.canonical_form_lam
  (ht : Γ.IsTight)
  (h : Typed Γ (Term.lam T t) (EType.type (CType.capt Cf (SType.forall T' E)))) :
  CSubtyp Γ T' T ∧
  Typed (Γ.var T') t E := by
  apply? Typed.canonical_form_lam'
  constructor

theorem Typed.canonical_form_tlam'
  (ht : Γ.IsTight)
  (hd : SType.Dealias Γ S0 (SType.tforall S' E))
  (he1 : t0 = Term.tlam S t)
  (he2 : E0 = EType.type (CType.capt Cf S0))
  (h : Typed Γ t0 E0) :
  SSubtyp Γ S' S ∧
  Typed (Γ.tvar (TBinding.bound S')) t E := by
  induction h <;> try (solve | cases he1 | cases he2)
  case tabs =>
    cases he1; cases he2
    cases hd
    constructor
    apply SSubtyp.refl
    trivial
  case sub hs ih =>
    subst he2
    cases hs
    rename_i hs
    cases hs
    rename_i hsc hs
    have ⟨S1, E1, hd3⟩ := SSubtyp.dealias_right_tforall hs ht hd
    have ih := ih ht hd3 he1 rfl
    have h := SSubtyp.sub_dealias_tforall_inv ht hd3 hd hs
    have ⟨hs1, ht1⟩ := ih
    have ⟨hs2, ht2⟩ := h
    apply And.intro
    { apply! SSubtyp.trans }
    { apply? Typed.sub
      apply! Typed.tnarrow }

theorem Typed.canonical_form_tlam
  (ht : Γ.IsTight)
  (h : Typed Γ (Term.tlam S t) (EType.type (CType.capt Cf (SType.tforall S' E)))) :
  SSubtyp Γ S' S ∧
  Typed (Γ.tvar (TBinding.bound S')) t E := by
  apply? Typed.canonical_form_tlam'
  constructor

theorem Typed.capp_inv'
  (he : t0 = Term.capp x c)
  (h : Typed Γ t0 E) :
  ∃ Cf F E0,
    Typed Γ (Term.var x) (EType.type (CType.capt Cf (SType.cforall F))) ∧
    E0 = F.copen c ∧
    ESubtyp Γ E0 E := by
  induction h <;> try (solve | cases he)
  case capp =>
    cases he
    repeat (apply Exists.intro)
    apply And.intro
    { trivial }
    apply And.intro
    { trivial }
    { apply ESubtyp.refl }
  case sub hs ih =>
    have ih := ih he
    have ⟨Cf, F, E0, hx, he0, hs0⟩ := ih
    have h := ESubtyp.trans hs0 hs
    aesop

theorem Typed.capp_inv
  (h : Typed Γ (Term.capp x c) E) :
  ∃ Cf F E0,
    Typed Γ (Term.var x) (EType.type (CType.capt Cf (SType.cforall F))) ∧
    E0 = F.copen c ∧
    ESubtyp Γ E0 E :=
  Typed.capp_inv' rfl h

theorem Typed.unbox_inv
  (h : Typed Γ (Term.unbox C x) E) :
  ∃ S,
    Typed Γ (Term.var x) (EType.type (CType.capt {} (SType.box (CType.capt C S)))) ∧
    E = EType.type (CType.capt C S) := sorry

theorem Typed.letin_inv' {Γ : Context n m k}
  (he : t0 = Term.letin t u)
  (h : Typed Γ t0 E) :
  ∃ T E0,
    Typed Γ t (EType.type T) ∧
    Typed (Γ.var T) u E0.weaken ∧
    ESubtyp Γ E0 E := by
  induction h <;> try (solve | cases he)
  case letin =>
    cases he
    repeat apply Exists.intro
    constructor; trivial
    constructor; trivial
    apply ESubtyp.refl
  case sub hs ih =>
    have ih := ih he
    obtain ⟨T, E0, ht, hu, hs0⟩ := ih
    have hs1 := ESubtyp.trans hs0 hs
    aesop

theorem Typed.letin_inv {Γ : Context n m k}
  (h : Typed Γ (Term.letin t u) E) :
  ∃ T E0,
    Typed Γ t (EType.type T) ∧
    Typed (Γ.var T) u E0.weaken ∧
    ESubtyp Γ E0 E :=
  Typed.letin_inv' rfl h

theorem Typed.letex_inv' {Γ : Context n m k}
  (he : t0 = Term.letex t u)
  (h : Typed Γ t0 E) :
  ∃ T E0,
    Typed Γ t (EType.ex T) ∧
    Typed ((Γ.cvar CBinding.bound).var T) u E0.cweaken.weaken ∧
    ESubtyp Γ E0 E := by
  induction h <;> try (solve | cases he)
  case letex =>
    cases he
    repeat apply Exists.intro
    constructor; trivial
    constructor; trivial
    apply ESubtyp.refl
  case sub hs ih =>
    have ih := ih he
    obtain ⟨T, E0, ht, hu, hs0⟩ := ih
    have hs1 := ESubtyp.trans hs0 hs
    aesop

theorem Typed.letex_inv {Γ : Context n m k}
  (h : Typed Γ (Term.letex t u) E) :
  ∃ T E0,
    Typed Γ t (EType.ex T) ∧
    Typed ((Γ.cvar CBinding.bound).var T) u E0.cweaken.weaken ∧
    ESubtyp Γ E0 E :=
  Typed.letex_inv' rfl h

theorem Typed.canonical_form_clam'
  (ht : Γ.IsTight)
  (hd : SType.Dealias Γ S0 (SType.cforall E))
  (he1 : t0 = Term.clam t)
  (he2 : E0 = EType.type (CType.capt Cf S0))
  (h : Typed Γ t0 E0) :
  Typed (Γ.cvar CBinding.bound) t E := by
  induction h <;> try (solve | cases he1 | cases he2)
  case cabs =>
    cases he1; cases he2
    cases hd
    trivial
  case sub hs ih =>
    subst he2
    cases hs
    rename_i hs
    cases hs
    rename_i hsc hs
    have ⟨E1, hd3⟩ := SSubtyp.dealias_right_cforall hs ht hd
    have ih := ih ht hd3 he1 rfl
    have h := SSubtyp.sub_dealias_cforall_inv ht hd3 hd hs
    apply! Typed.sub

theorem Typed.canonical_form_clam
  (ht : Γ.IsTight)
  (h : Typed Γ (Term.clam t) (EType.type (CType.capt Cf (SType.cforall E)))) :
  Typed (Γ.cvar CBinding.bound) t E := by
  apply? Typed.canonical_form_clam'
  constructor

theorem Typed.canonical_form_boxed
  (ht : Γ.IsTight)
  (h : Typed Γ (Term.boxed x) (EType.type (CType.capt {} (SType.box (CType.capt C S))))) :
  Typed Γ (Term.var x) (EType.type (CType.capt C S)) := sorry

end Capless
