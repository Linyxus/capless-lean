import Capless.Tactics
import Capless.Typing
import Capless.Subtyping.Basic
import Capless.Subcapturing.Basic
import Capless.Inversion.Subtyping
import Capless.Subst.Term.Typing
import Capless.Subst.Type.Typing
import Capless.Subst.Capture.Subtyping
import Capless.Narrowing.Typing
import Capless.Weakening.Subcapturing
import Capless.Inversion.Context
namespace Capless

theorem Typed.app_inv'
  (he : t0 = Term.app x y)
  (h : Typed Γ t0 E Ct0) :
  ∃ T Cf F E0, Typed Γ (Term.var x) (EType.type (CType.capt Cf (SType.forall T F))) {x=x}
    ∧ Typed Γ (Term.var y) (EType.type T) {x=y}
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
      repeat (any_goals apply And.intro)
      all_goals try assumption
      { apply! ESubtyp.trans }

theorem Typed.app_inv
  (h : Typed Γ (Term.app x y) E Ct) :
  ∃ T Cf F E0, Typed Γ (Term.var x) (EType.type (CType.capt Cf (SType.forall T F))) {x=x}
    ∧ Typed Γ (Term.var y) (EType.type T) {x=y}
    ∧ E0 = F.open y
    ∧ ESubtyp Γ E0 E :=
  Typed.app_inv' rfl h

theorem Typed.tapp_inv'
  (he : t0 = Term.tapp x X)
  (h : Typed Γ t0 E Ct) :
  ∃ Cf F E0,
    Typed Γ (Term.var x) (EType.type (CType.capt Cf (SType.tforall (SType.tvar X) F))) {x=x}
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
  case sub hs ih =>
    have ih := ih he
    have ⟨Cf, F, E0, hx, he0, hs0⟩ := ih
    have h := ESubtyp.trans hs0 hs
    aesop

theorem Typed.tapp_inv
  (h : Typed Γ (Term.tapp x X) E Ct) :
  ∃ Cf F E0,
    Typed Γ (Term.var x) (EType.type (CType.capt Cf (SType.tforall (SType.tvar X) F))) {x=x}
    ∧ E0 = F.topen X
    ∧ ESubtyp Γ E0 E :=
  Typed.tapp_inv' rfl h

theorem Typed.var_inv'
  (he1 : t0 = Term.var x)
  (he2 : E0 = EType.type T)
  (h : Typed Γ t0 E0 Ct0) (hb : Γ.Bound x T0) :
  ∃ C0 S0, Γ.Bound x (S0^C0) ∧ (Γ ⊢ (S0^{x=x}) <: T) := by
  induction h <;> try (solve | cases he1 | cases he2)
  case var C0 S0 hb =>
    cases he1; cases he2
    apply Exists.intro C0
    apply Exists.intro S0
    constructor
    { trivial }
    { apply CSubtyp.refl }
  case label hbl =>
    exfalso
    cases he1
    apply Context.bound_lbound_absurd hb hbl
  case sub hs ih =>
    have h := ESubtyp.sub_type_inv' he2 hs
    have ⟨T1, he, hs1⟩ := h
    have ih := ih he1 he hb
    have ⟨C0, S0, hb, hs0⟩ := ih
    apply Exists.intro C0
    apply Exists.intro S0
    constructor
    { assumption }
    { apply CSubtyp.trans <;> assumption }

theorem Typed.var_inv
  (h : Typed Γ (Term.var x) (EType.type T) Ct) (hb : Γ.Bound x T0) :
  ∃ C0 S0, Γ.Bound x (CType.capt C0 S0) ∧ CSubtyp Γ (CType.capt {x=x} S0) T := by
  apply Typed.var_inv' rfl rfl h hb

theorem Typed.canonical_form_lam'
  (ht : Γ.IsTight)
  (he1 : t0 = Term.lam T t) (hd2 : SType.Dealias Γ S0 (SType.forall T' E))
  (he2 : E0 = EType.type (CType.capt Cf S0))
  (h : Typed Γ t0 E0 Ct0) :
  CSubtyp Γ T' T ∧
  Typed (Γ.var T') t E (Cf.weaken ∪ {x=0}) := by
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
    { apply Typed.sub <;> try easy
      apply ht1.narrow
      assumption
      apply Subcapt.join
      { apply hsc.weaken }
      { apply Subcapt.refl } }

theorem Typed.canonical_form_lam
  (ht : Γ.IsTight)
  (h : Typed Γ (Term.lam T t) (EType.type ((∀(x:T')E)^Cf)) Ct) :
  CSubtyp Γ T' T ∧
  Typed (Γ.var T') t E (Cf.weaken ∪ {x=0}) := by
  apply Typed.canonical_form_lam' <;> try trivial
  constructor

theorem Typed.canonical_form_tlam'
  (ht : Γ.IsTight)
  (hd : SType.Dealias Γ S0 (SType.tforall S' E))
  (he1 : t0 = Term.tlam S t)
  (he2 : E0 = EType.type (CType.capt Cf S0))
  (h : Typed Γ t0 E0 Ct0) :
  SSubtyp Γ S' S ∧
  Typed (Γ.tvar (TBinding.bound S')) t E Cf := by
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
    { constructor
      apply? Typed.sub
      apply ht1.tnarrow; assumption; apply Subcapt.refl
      apply hsc.tweaken
      apply ESubtyp.refl }

theorem Typed.canonical_form_tlam
  (ht : Γ.IsTight)
  (h : Typed Γ (Term.tlam S t) (EType.type ((∀[X<:S']E)^Cf)) Ct0) :
  SSubtyp Γ S' S ∧
  Typed (Γ.tvar (TBinding.bound S')) t E Cf := by
  apply Typed.canonical_form_tlam' <;> try trivial
  constructor

theorem Typed.capp_inv'
  (he : t0 = Term.capp x c)
  (h : Typed Γ t0 E Ct0) :
  ∃ Cf F E0,
    Typed Γ (Term.var x) (EType.type (CType.capt Cf (SType.cforall F))) {x=x} ∧
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
  (h : Typed Γ (Term.capp x c) E Ct0) :
  ∃ Cf F E0,
    Typed Γ (Term.var x) (EType.type (CType.capt Cf (SType.cforall F))) {x=x} ∧
    E0 = F.copen c ∧
    ESubtyp Γ E0 E :=
  Typed.capp_inv' rfl h

theorem Typed.unbox_inv'
  (he : t0 = Term.unbox C x)
  (h : Typed Γ t0 E Ct0) :
  ∃ S,
    Typed Γ (Term.var x) (EType.type (CType.capt {} (SType.box (CType.capt C S)))) {} ∧
    ESubtyp Γ (EType.type (CType.capt C S)) E := by
  induction h <;> try (solve | cases he)
  case unbox =>
    cases he
    apply Exists.intro
    constructor; trivial
    apply ESubtyp.refl
  case sub hs ih =>
    have ih1 := ih he
    obtain ⟨S, hx, hsub⟩ := ih1
    apply Exists.intro S
    constructor; trivial
    apply? ESubtyp.trans

theorem Typed.unbox_inv
  (h : Typed Γ (C o- x) E Ct) :
  ∃ S,
    Typed Γ (Term.var x) (EType.type ((SType.box (S^C))^{})) {} ∧
    ESubtyp Γ (EType.type (CType.capt C S)) E :=
  Typed.unbox_inv' rfl h

theorem Typed.letin_inv' {Γ : Context n m k}
  (he : t0 = Term.letin t u)
  (h : Typed Γ t0 E Ct0) :
  ∃ T E0 C0,
    Typed Γ t (EType.type T) C0 ∧
    Typed (Γ.var T) u E0.weaken C0.weaken ∧
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
    obtain ⟨T, E0, C0, ht, hu, hs0⟩ := ih
    have hs1 := ESubtyp.trans hs0 hs
    aesop

theorem Typed.letin_inv {Γ : Context n m k}
  (h : Typed Γ (Term.letin t u) E Ct) :
  ∃ T E0 C0,
    Typed Γ t (EType.type T) C0 ∧
    Typed (Γ.var T) u E0.weaken C0.weaken ∧
    ESubtyp Γ E0 E :=
  Typed.letin_inv' rfl h

theorem Typed.letex_inv' {Γ : Context n m k}
  (he : t0 = Term.letex t u)
  (h : Typed Γ t0 E Ct0) :
  ∃ T E0 C0,
    Typed Γ t (EType.ex T) C0 ∧
    Typed ((Γ.cvar CBinding.bound).var T) u E0.cweaken.weaken C0.cweaken.weaken ∧
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
    obtain ⟨T, E0, C0, ht, hu, hs0⟩ := ih
    have hs1 := ESubtyp.trans hs0 hs
    aesop

theorem Typed.letex_inv {Γ : Context n m k}
  (h : Typed Γ (Term.letex t u) E Ct) :
  ∃ T E0 C0,
    Typed Γ t (EType.ex T) C0 ∧
    Typed ((Γ.cvar CBinding.bound).var T) u E0.cweaken.weaken C0.cweaken.weaken ∧
    ESubtyp Γ E0 E :=
  Typed.letex_inv' rfl h

theorem Typed.bindt_inv' {Γ : Context n m k}
  (he : t0 = Term.bindt T t)
  (h : Typed Γ t0 E Ct0) :
  ∃ E0 C0,
    Typed (Γ.tvar (TBinding.inst T)) t E0.tweaken C0 ∧
    ESubtyp Γ E0 E := by
  induction h <;> try (solve | cases he)
  case bindt =>
    cases he
    apply Exists.intro; apply Exists.intro
    constructor; trivial
    apply ESubtyp.refl
  case sub hs ih =>
    have ih := ih he
    obtain ⟨E0, C0, ht, hs0⟩ := ih
    apply Exists.intro E0; apply Exists.intro
    constructor; trivial
    apply? ESubtyp.trans

theorem Typed.bindt_inv {Γ : Context n m k}
  (h : Typed Γ (let X=T in t) E Ct) :
  ∃ E0 C0,
    Typed (Γ,X:=T) t E0.tweaken C0 ∧
    (Γ ⊢ E0 <:e E) :=
  Typed.bindt_inv' rfl h

theorem Typed.bindc_inv' {Γ : Context n m k}
  (he : t0 = Term.bindc C t)
  (h : Typed Γ t0 E Ct) :
  ∃ E0 C0,
    Typed (Γ.cvar (CBinding.inst C)) t E0.cweaken (CaptureSet.cweaken C0) ∧
    ESubtyp Γ E0 E := by
  induction h <;> try (solve | cases he)
  case bindc =>
    cases he
    repeat apply Exists.intro
    constructor; trivial
    apply ESubtyp.refl
  case sub hs ih =>
    have ih := ih he
    obtain ⟨E0, C0, ht, hs0⟩ := ih
    repeat apply Exists.intro
    constructor; trivial
    apply? ESubtyp.trans

theorem Typed.bindc_inv {Γ : Context n m k}
  (h : Typed Γ (let c=C in t) E Ct) :
  ∃ E0 C0,
    Typed (Γ,c:=C) t E0.cweaken (CaptureSet.cweaken C0) ∧
    (Γ ⊢ E0 <:e E) :=
  Typed.bindc_inv' rfl h

theorem Typed.canonical_form_clam'
  (ht : Γ.IsTight)
  (hd : SType.Dealias Γ S0 (SType.cforall E))
  (he1 : t0 = Term.clam t)
  (he2 : E0 = EType.type (CType.capt Cf S0))
  (h : Typed Γ t0 E0 Ct0) :
  Typed (Γ.cvar CBinding.bound) t E Cf.cweaken := by
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
    constructor
    apply Typed.sub
    apply ih
    apply Subcapt.refl
    trivial
    apply hsc.cweaken
    apply ESubtyp.refl

theorem Typed.canonical_form_clam
  (ht : Γ.IsTight)
  (h : Typed Γ (Term.clam t) (EType.type ((∀[c]E)^Cf)) Ct) :
  Typed (Γ.cvar CBinding.bound) t E Cf.cweaken := by
  apply Typed.canonical_form_clam' <;> try trivial
  constructor

theorem Typed.canonical_form_boxed'
  (ht : Γ.IsTight)
  (hd : SType.Dealias Γ S0 (SType.box (CType.capt C S)))
  (he1 : t0 = Term.boxed x)
  (he2 : E0 = EType.type (CType.capt Cf S0))
  (h : Typed Γ t0 E0 Ct) :
  Typed Γ (Term.var x) (EType.type (CType.capt C S)) {x=x} := by
  induction h <;> try (solve | cases he1 | cases he2)
  case box =>
    cases he1; cases he2; cases hd
    trivial
  case sub hs ih =>
    subst he2
    cases hs
    rename_i hs
    cases hs
    rename_i hsc hs
    have ⟨T1, hd3⟩ := SSubtyp.dealias_right_boxed hs ht hd
    cases T1
    have ih := ih ht hd3 he1 rfl
    have h := SSubtyp.sub_dealias_boxed_inv ht hd3 hd hs
    apply Typed.sub
    exact ih
    apply Subcapt.refl
    constructor; trivial

theorem Typed.canonical_form_boxed
  (ht : Γ.IsTight)
  (h : Typed Γ (Term.boxed x) (EType.type (CType.capt Cb (SType.box (CType.capt C S)))) Ct) :
  Typed Γ (Term.var x) (EType.type (CType.capt C S)) {x=x} :=
  Typed.canonical_form_boxed' ht (by constructor) rfl rfl h

theorem Typed.canonical_form_pack'
  (ht : Γ.IsTight)
  (he1 : t0 = Term.pack C x)
  (he2 : E0 = EType.ex T)
  (h : Typed Γ t0 E0 Ct) :
  Typed (Γ.cvar (CBinding.inst C)) (Term.var x) (EType.type T) {x=x} := by
  induction h <;> try (solve | cases he1 | cases he2)
  case pack =>
    cases he1; cases he2
    trivial
  case sub hs ih =>
    subst he2
    cases hs
    rename_i hs
    have ih := ih ht he1 rfl
    apply Typed.sub
    exact ih
    apply Subcapt.refl
    constructor
    apply hs.cinstantiate

theorem Typed.canonical_form_pack
  (ht : Γ.IsTight)
  (h : Typed Γ (Term.pack C x) (EType.ex T) Ct) :
  Typed (Γ.cvar (CBinding.inst C)) (Term.var x) (EType.type T) {x=x} :=
  Typed.canonical_form_pack' ht rfl rfl h

theorem Typed.forall_inv' {v : Term n m k}
  (ht : Γ.IsTight)
  (hd : SType.Dealias Γ S0 (SType.forall T E))
  (he : E0 = EType.type (CType.capt Cv S0))
  (hv : v.IsValue)
  (ht : Typed Γ v E0 Ct) :
  ∃ T0 t, v = Term.lam T0 t := by
  induction ht <;> try (solve | cases hv | cases he | cases hv; cases he; cases hd)
  case sub hsub ih =>
    subst he
    cases hsub
    rename_i hsub
    cases hsub
    rename_i hsc hss
    have ⟨T1, E1, hd1⟩ := SSubtyp.dealias_right_forall hss ht hd
    aesop
  case abs => aesop

theorem Typed.forall_inv {v : Term n m k}
  (hg : Γ.IsTight)
  (hv : v.IsValue)
  (ht : Typed Γ v (EType.type (CType.capt Cv (SType.forall T E))) Ct) :
  ∃ T0 t, v = Term.lam T0 t :=
  Typed.forall_inv' hg (by constructor) rfl hv ht

theorem Typed.tforall_inv' {v : Term n m k}
  (ht : Γ.IsTight)
  (hd : SType.Dealias Γ S0 (SType.tforall X E))
  (he : E0 = EType.type (CType.capt Cv S0))
  (hv : v.IsValue)
  (ht : Typed Γ v E0 Ct) :
  ∃ X t, v = Term.tlam X t := by
  induction ht <;> try (solve | cases hv | cases he | cases hv; cases he; cases hd)
  case sub hsub ih =>
    subst he
    cases hsub
    rename_i hsub
    cases hsub
    rename_i hsc hss
    have ⟨T1, E1, hd1⟩ := SSubtyp.dealias_right_tforall hss ht hd
    aesop
  case tabs => aesop

theorem Typed.tforall_inv {v : Term n m k}
  (hg : Γ.IsTight)
  (hv : v.IsValue)
  (ht : Typed Γ v (EType.type (CType.capt Cv (SType.tforall X E))) Ct) :
  ∃ X t, v = Term.tlam X t :=
  Typed.tforall_inv' hg (by constructor) rfl hv ht

theorem Typed.cforall_inv' {v : Term n m k}
  (ht : Γ.IsTight)
  (hd : SType.Dealias Γ S0 (SType.cforall E))
  (he : E0 = EType.type (CType.capt Cv S0))
  (hv : v.IsValue)
  (ht : Typed Γ v E0 Ct) :
  ∃ t, v = Term.clam t := by
  induction ht <;> try (solve | cases hv | cases he | cases hv; cases he; cases hd)
  case sub hsub ih =>
    subst he
    cases hsub
    rename_i hsub
    cases hsub
    rename_i hsc hss
    have ⟨E1, hd1⟩ := SSubtyp.dealias_right_cforall hss ht hd
    aesop
  case cabs => aesop

theorem Typed.cforall_inv {v : Term n m k}
  (hg : Γ.IsTight)
  (hv : v.IsValue)
  (ht : Typed Γ v (EType.type (CType.capt Cv (SType.cforall E))) Ct) :
  ∃ t, v = Term.clam t :=
  Typed.cforall_inv' hg (by constructor) rfl hv ht

theorem Typed.boxed_inv' {v : Term n m k}
  (ht : Γ.IsTight)
  (hd : SType.Dealias Γ S0 (SType.box (CType.capt C S)))
  (he : E0 = EType.type (CType.capt Cv S0))
  (hv : v.IsValue)
  (ht : Typed Γ v E0 Ct) :
  ∃ t, v = Term.boxed t := by
  induction ht <;> try (solve | cases hv | cases he | cases hv; cases he; cases hd)
  case sub hsub ih =>
    subst he
    cases hsub
    rename_i hsub
    cases hsub
    rename_i hsc hss
    have ⟨T1, hd1⟩ := SSubtyp.dealias_right_boxed hss ht hd
    cases T1
    aesop
  case box => aesop

theorem Typed.boxed_inv {v : Term n m k}
  (hg : Γ.IsTight)
  (hv : v.IsValue)
  (ht : Typed Γ v (EType.type (CType.capt Cv (SType.box (CType.capt C S)))) Ct):
  ∃ t, v = Term.boxed t :=
  Typed.boxed_inv' hg (by constructor) rfl hv ht

theorem Typed.var_inv_capt'
  (he : t0 = Term.var x)
  (hx : Typed Γ t0 E Cx) :
  Γ ⊢ ({x=x}) <:c Cx := by
  induction hx <;> try (solve | cases he)
  case var => cases he; apply Subcapt.refl
  case label => cases he; apply Subcapt.refl
  case sub ih =>
    have ih := ih he
    apply Subcapt.trans <;> easy

theorem Typed.var_inv_capt
  (hx : Typed Γ (Term.var x) E Cx) :
  Γ ⊢ ({x=x}) <:c Cx :=
  Typed.var_inv_capt' rfl hx

theorem Typed.app_inv_capt'
  (he : t0 = Term.app x y)
  (ht : Typed Γ t0 E Ct) :
  Γ ⊢ ({x=x}∪{x=y}) <:c Ct := by
  induction ht <;> try (solve | cases he)
  case app => cases he; apply Subcapt.refl
  case sub ih =>
    have ih := ih he
    apply! Subcapt.trans

theorem Typed.app_inv_capt
  (ht : Typed Γ (Term.app x y) E Ct) :
  Γ ⊢ ({x=x}∪{x=y}) <:c Ct :=
  Typed.app_inv_capt' rfl ht

theorem Typed.tapp_inv_capt'
  (he : t0 = Term.tapp x X)
  (ht : Typed Γ t0 E Ct) :
  Γ ⊢ ({x=x}) <:c Ct := by
  induction ht <;> try (solve | cases he)
  case tapp => cases he; apply Subcapt.refl
  case sub ih =>
    have ih := ih he
    apply! Subcapt.trans

theorem Typed.tapp_inv_capt
  (ht : Typed Γ (Term.tapp x X) E Ct) :
  Γ ⊢ ({x=x}) <:c Ct :=
  Typed.tapp_inv_capt' rfl ht

theorem Typed.capp_inv_capt'
  (he : t0 = Term.capp x c)
  (ht : Typed Γ t0 E Ct) :
  Γ ⊢ ({x=x}) <:c Ct := by
  induction ht <;> try (solve | cases he)
  case capp => cases he; apply Subcapt.refl
  case sub ih =>
    have ih := ih he
    apply! Subcapt.trans

theorem Typed.capp_inv_capt
  (ht : Typed Γ (Term.capp x c) E Ct) :
  Γ ⊢ ({x=x}) <:c Ct :=
  Typed.capp_inv_capt' rfl ht

end Capless
