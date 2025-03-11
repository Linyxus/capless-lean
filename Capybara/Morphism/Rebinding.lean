import Capless.Tactics
import Capybara.Syntax
import Capybara.Morphism.Core
namespace Capybara

/-!
# Rebinding

## Definition
A rebinding is a morphism from a source context `Γ` to a target context `Δ` that maps each binding in `Γ` to an equivalent one in `Δ`.
-/
structure Rebinding (Γ : Context n m k) (Δ : Context n' m' k') where
  ρ : Renaming n m k n' m' k'
  var : ∀ {x T}, Γ.Lookup x T -> Δ.Lookup (ρ.var x) (T.rename ρ)
  tvar : ∀ {X S}, Γ.LookupT X S -> Δ.LookupT (ρ.tvar X) (S.rename ρ)
  cvar : ∀ {c K}, Γ.LookupC c K -> Δ.LookupC (ρ.cvar c) (K.rename ρ.asCapt)
  -- A rebinding is injective on fresh capture variables, as mapping two distinct
  -- fresh capture variables to the same variable breaks the separation invariant.
  -- This is needed to prove the `s_fresh` case of `RootSeparation.rebind`.
  fresh_inj : ∀ {c1 c2},
    Γ.LookupC c1 (CBinding.param CKind.Fresh) -> Γ.LookupC c2 (CBinding.param CKind.Fresh) ->
    (c1 ≠ c2) -> (ρ.cvar c1 ≠ ρ.cvar c2)

/-!
## Extensions
The following methods lift rebindings to environments with more bindings.
-/
def Rebinding.ext (θ : Rebinding Γ Δ) : Rebinding (Γ,x:T) (Δ,x:T.rename θ.ρ) := by
  constructor
  case ρ => exact θ.ρ.ext
  case var =>
    intro x T hb
    cases hb with
    | here =>
      simp [Renaming.ext_var_zero]
      simp [<-CType.rename_weaken]
      constructor
    | there h =>
      simp [Renaming.ext_var_succ]
      simp [<-CType.rename_weaken]
      constructor
      apply θ.var; easy
  case tvar =>
    intro X S hb
    cases hb
    case there hb =>
      simp [<-TBinding.rename_weaken]
      constructor
      apply θ.tvar; easy
  case cvar =>
    intro c B hb
    cases hb
    case there hb =>
      simp [<-CBinding.rename_weaken]
      constructor
      apply θ.cvar; easy
  case fresh_inj =>
    intro c1 c2 hc1 hc2 hneq
    have hc1' := Context.var_lookupc_fresh_inv hc1
    have hc2' := Context.var_lookupc_fresh_inv hc2
    apply θ.fresh_inj <;> aesop

def Rebinding.text (θ : Rebinding Γ Δ) : Rebinding (Γ,X:B) (Δ,X:B.rename θ.ρ) := by
  constructor
  case ρ => exact θ.ρ.text
  case var =>
    intro x T hb
    cases hb
    case tthere hb =>
      simp [<-CType.rename_tweaken]
      constructor
      apply θ.var; easy
  case tvar =>
    intro X B hb
    cases hb
    case here =>
      simp [<-TBinding.rename_tweaken]
      constructor
    case tthere hb =>
      simp [<-TBinding.rename_tweaken]
      constructor
      apply θ.tvar; easy
  case cvar =>
    intro c B hb
    cases hb
    case tthere hb =>
      simp
      constructor
      apply θ.cvar; easy
  case fresh_inj =>
    intro c1 c2 hc1 hc2 hneq
    have hc1' := Context.tvar_lookupc_inv hc1
    have hc2' := Context.tvar_lookupc_inv hc2
    apply θ.fresh_inj <;> aesop

def Rebinding.cext (θ : Rebinding Γ Δ) : Rebinding (Γ,c:K) (Δ,c:K.rename θ.ρ.asCapt) := by
  constructor
  case ρ => exact θ.ρ.cext
  case var =>
    intro x T hb
    cases hb
    case cthere hb =>
      simp [<-CType.rename_cweaken]
      constructor
      apply θ.var; easy
  case tvar =>
    intro X B hb
    cases hb
    case cthere hb =>
      simp [<-TBinding.rename_cweaken]
      constructor
      apply θ.tvar; easy
  case cvar =>
    intro c K hb
    cases hb
    case here =>
      simp [<-CBinding.rename_cweaken]
      constructor
    case cthere hb =>
      simp [<-CBinding.rename_cweaken]
      constructor
      apply θ.cvar; easy
  case fresh_inj =>
    intro c1 c2 hc1 hc2 hneq
    have h1 := Context.cvar_lookupc_inv hc1
    have h2 := Context.cvar_lookupc_inv hc2
    match h1, h2 with
    | Or.inl ⟨h1,_⟩,  Or.inl ⟨h2,_⟩ => aesop
    | Or.inl ⟨h1,_⟩, Or.inr ⟨_, _, _, h2, _⟩ =>
      subst_vars
      simp [Renaming.cext, FinFun.ext]
      intro h; cases h
    | Or.inr ⟨_, _, _, h1, _⟩, Or.inl ⟨h2,_⟩ =>
      subst_vars
      simp [Renaming.cext, FinFun.ext]
      intro h; cases h
    | Or.inr ⟨c1, b1, hb1, h1, he1⟩, Or.inr ⟨c2, b2, hb2, h2, he2⟩ =>
      cases h1; cases h2
      cases b1 <;> try cases he1
      rename_i K; cases K <;> cases he1
      cases b2 <;> try cases he2
      rename_i K; cases K <;> cases he2
      simp [Renaming.cext, FinFun.ext]
      intro h
      apply θ.fresh_inj
      exact hb1; exact hb2
      aesop
      easy

end Capybara
