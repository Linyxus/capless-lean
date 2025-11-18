import Lake
open Lake DSL

package «capless» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩,
    ⟨`linter.unusedVariables, false⟩
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.25.1"

require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.25.1"

require «importGraph» from git -- requires graphviz
  "https://github.com/leanprover-community/import-graph" @ "v4.25.1"

@[default_target]
lean_lib «Capless» where
  -- add any library configuration options here
