import Capless.Subcapturing
namespace Capless

theorem Subcapt.refl :
  Subcapt Γ C C := by
  apply subset
  apply CaptureSet.subset_refl

theorem Context.cvar_bound_var_inv_type {Γ : Context n m k}
  (hb : (Γ.cvar b).Bound x (EType.type (CType.capt C S))) :
  ∃ C' S',
    C = C'.cweaken
    ∧ S = S'.cweaken
    ∧ Context.Bound Γ x (EType.type (CType.capt C' S')) := by
    have ⟨E0, hb, heq⟩ := Context.cvar_bound_var_inv hb
    have ⟨C0, S0, he1, he2, he3⟩ := EType.cweaken_eq_inv heq
    exists C0, S0
    aesop

theorem Context.cvar_bound_var_inv_ex {Γ : Context n m k}
  (hb : (Γ.cvar b).Bound x (EType.ex (CType.capt C S))) :
  ∃ C' S',
    C = C'.cweaken1
    ∧ S = S'.cweaken1
    ∧ Context.Bound Γ x (EType.ex (CType.capt C' S')) := by
    have ⟨E0, hb, heq⟩ := Context.cvar_bound_var_inv hb
    have ⟨C0, S0, he1, he2, he3⟩ := EType.ex_cweaken_eq_inv heq
    exists C0, S0
    aesop

theorem Context.cvar_bound_var_inv_exp {Γ : Context n m k}
  (hb : (Γ.cvar b).Bound x (EType.exp c T)) :
  ∃ c' T',
    c = c'.succ ∧ T = T'.cweaken
    ∧ Context.Bound Γ x (EType.exp c' T') := by
    have ⟨E0, hb, heq⟩ := Context.cvar_bound_var_inv hb
    sorry

-- theorem Subcapt.subcapt_cweaken' {Γ : Context n m k}
--   (he1 : C = C2.cweaken)
--   (he2 : Γ0 = Γ.cvar CBinding.bound)
--   (h : Subcapt Γ0 C1 C) :
--   ∃ C0, C1 = C0.cweaken ∧ Subcapt Γ C0 C2 := by
--   induction h generalizing C2
--   case trans ih1 ih2 =>
--     subst he1 he2
--     have ih2 := ih2 rfl rfl
--     let ⟨C0, he, h⟩ := ih2
--     have ih1 := ih1 he rfl
--     let ⟨C0', he', h'⟩ := ih1
--     apply Exists.intro C0'
--     constructor; trivial
--     apply trans <;> trivial
--   case subset hsub =>
--     subst he1 he2
--     have h := CaptureSet.subset_cweaken hsub
--     let ⟨C0, he⟩ := h
--     apply Exists.intro C0
--     constructor <;> try trivial
--     subst he
--     apply subset; apply CaptureSet.cweaken_subset_subset
--     trivial
--   case union ih1 ih2 =>
--     have ih1 := ih1 he1 he2
--     have ih2 := ih2 he1 he2
--     let ⟨D0, h1, h2⟩ := ih1
--     let ⟨D1, h3, h4⟩ := ih2
--     apply Exists.intro (D0 ∪ D1)
--     subst h1 h3
--     apply And.intro
--     simp [CaptureSet.cweaken_union]
--     apply union <;> trivial
--   case var x _ _ hb =>
--     rw [he2] at hb
--     have ⟨C0, S0, he1', he2', hb1⟩ := Context.cvar_bound_var_inv_type hb
--     exists {x}
--     simp [CaptureSet.cweaken, CaptureSet.crename_singleton]
--     apply var
--     rw [he1] at he1'
--     have he := CaptureSet.cweaken_inj he1'
--     subst he
--     exact hb1
--   case evar x _ _ hb =>
--     exists {x}
--     simp [CaptureSet.cweaken, CaptureSet.crename_singleton]
--     rw [he2] at hb
--     have ⟨C0, S0, he1', he2', hb1⟩ := Context.cvar_bound_var_inv_ex hb
--     apply evar
--     rw [he1] at he1'
--     have he3 := CaptureSet.cweaken1_cweaken_eq he1'
--     rw [he3] at he1'
--     have he4 := CaptureSet.cweaken_inj he1'
--     subst he4
--     trivial
--   case cinstl hb =>
--     have ⟨c0, eq1, eq2⟩ := CaptureSet.csingleton_cweaken_eq_inv he1
--     rw [he2] at hb
--     have ⟨c1, C0, h1, h2, h3⟩ := Context.cvar_bound_cvar_inst_inv hb
--     rw [eq1] at h1
--     rw [Fin.succ_inj] at h1
--     subst h1
--     exists C0
--     constructor; trivial
--     subst eq2
--     apply cinstl
--     exact h3
--   case cinstr hb =>
--     rw [he2] at hb
--     have ⟨c1, C0, h1, h2, h3⟩ := Context.cvar_bound_cvar_inst_inv hb
--     rw [he1] at h2
--     apply CaptureSet.cweaken_inj at h2
--     subst h2
--     apply Exists.intro (CaptureSet.csingleton c1)
--     constructor
--     simp [h1, CaptureSet.cweaken_csingleton]
--     apply cinstr; exact h3
--   case reachl => sorry
--   case reachr => sorry

-- theorem Subcapt.subcapt_cweaken {Γ : Context n m k}
--   (h : Subcapt (Γ.cvar CBinding.bound) C1 C2.cweaken) :
--   ∃ C0, C1 = C0.cweaken ∧ Subcapt Γ C0 C2 := by sorry

-- end Capless
