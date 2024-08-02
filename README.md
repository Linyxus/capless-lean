# A Lean Mechanisation of Capless

This mechanisation takes a extrinsically-typed and DeBruijn-indexed representation. `Capless.lean` is the index file.

## Well-Scoped Terms

The inductive data types are indexed by the number of bound variables. For instance, a term of type `Term n m k` has `n`, `m`, `k` term, type, and capture variables bound respectively.

This, basically, enforces the well-formedness of any syntactic constructs by construction. So no well-formedness judgements are needed.

## Monadic Normal Forms

The calculus is in Monadic Normal Form (MNF). On the paper, only term variables are in MNF, yet type and capture applications require general substitution (substitute a type variable for a shape type, or a capture variable for a capture set).

In the calculus MNF is extended to type and capture variables. So we have added binding forms for them.

Translating non-MNF type and capture variables to an MNF one is trivial.

With this change, the infrastructure is greatly simplified: renaming is sufficient for all syntactic constructs.

## Substitution Theorems

Substitution theorems are stratified into two layers.

### Renaming

The first layer is renaming, of which relevant proof scripts are located in `Capless/Renaming`. The renaming theorems show that environment renaming morphisms preserve typing judgements. For instance, given:
(1) A typing judgement `h : Γ ⊢ t : E`,
(2) a renaming morphism `ρ : VarRename Γ f Δ`, which basically says that for any `x : E ∈ Γ`, there is a corresponding binding `f x : E.rename f ∈ Δ` in the mapped context,
then with the renaming theorem we derive that `Δ ⊢ t.rename f : E.rename f`.

With the renaming theorems, structural rules like weakening and permutation could be proven.

### Substitution

The second layer is the actual substitution, whose relevant proof scripts are located in `Capless/Subst`. The substitution theorems show that environment substitution morphisms preserve typing judgements. Similar to the renaming layer, given:
(1) A typing judgement `h : Γ ⊢ t : E`,
(2) a substitution morphism `σ : VarSubst Γ f Δ`, which basically says that for any `x : E ∈ Γ` one could derive `Δ ⊢ x : E` in the mapped context,
then it can be derived that `Δ ⊢ t.rename f : E.rename f`.

These are the actual substitution theorems that the preservation proof relies on. This layer depends on the first one.

## Roadmap

- [x] Renaming
  - [x] Term
    - [x] Subcapturing
    - [x] Subtyping
    - [x] Typing
  - [x] Type
    - [x] Subcapturing
    - [x] Subtyping
    - [x] Typing
  - [x] Capture
    - [x] Subcapturing
    - [x] Subtyping
    - [x] Typing
- [X] Substitution
  - [x] Term
    - [x] Subcapturing
    - [x] Subtyping
    - [x] Typing
  - [X] Type
    - [X] Subcapturing
    - [X] Subtyping
    - [X] Typing
  - [X] Capture
    - [X] Subcapturing
    - [X] Subtyping
    - [X] Typing
- [x] Store lookup
  - [x] Lookup inversion
  - [x] Canonical forms (WIP)
    - [x] Term abstraction
    - [x] Type abstraction
    - [x] Capture abstraction
    - [x] Box
    - [x] Pack
- [x] Soundness
  - [x] Preservation
  - [x] Progress




