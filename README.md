# System Capless

This is the Lean 4 mechanization of System Capless, including the scoped capability extension.

The entry file is `Capless.lean`. The main soundness results (progress and preservation) locate in the `Capless/Soundness` directory.

To compile the proof, run
```bash
lake cache exe get
lake build
```
This first retrieves build cache for `mathlib` (which saves significantly the build time but is optional if that doesn't work), and then build the proof. It may take sometime.
