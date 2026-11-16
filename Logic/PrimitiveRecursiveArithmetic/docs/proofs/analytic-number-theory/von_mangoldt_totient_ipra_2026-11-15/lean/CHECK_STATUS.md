# Lean check status

The Lean files are **scaffolds, not completed proofs**.

- `VonMangoldtTotientHost.lean` contains several `sorry` obligations.
- `VonMangoldtTotientObjectTheory.lean` uses `axiom` declarations to expose intended theorem types and demonstrate the faithful transfer endpoint.
- Lean and Lake were not installed in the artifact-generation environment, so neither file was compiled here.
- The exact implementation path and no-new-axiom acceptance criteria are in `FORMALIZATION_PLAN.md`.

A completed development should remove all `sorry`/new `axiom` declarations and pass an axiom audit in the pinned ProveIt workspace.
