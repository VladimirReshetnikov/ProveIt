# Workstream registry: `codex/fabius-both-papers`

This file implements the per-branch registry fallback in
[`../COLLABORATION.md`](../COLLABORATION.md).

```text
SYNC Fabius
worktree/task: /root — signed-global primitive-recursive spline evaluator
branch/base: codex/fabius-both-papers synchronized with origin/main at
  72f80664131bc38be4dc68edefd75fca1a5c349a
writing: Lean/FabiusFunction/FabiusComputability.lean,
  Lean/FabiusFunction/FabiusComputableSpline.lean, README.md,
  docs/Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.{tex,pdf},
  docs/fabius_lean_walkthrough/fabius_lean_walkthrough.{tex,pdf}, this registry
reading: existing bounded spline evaluator and signed-global uniform spline,
  Lipschitz, effective-continuity, and dyadic-name APIs
expected API: signed-rational nearest rounding with half ties away from zero;
  primitive-recursive global
  spline evaluator with the same five-guard-unit error; general and canonical
  sequential-computability and computable-real-function theorems for
  `extendedFabius` and `globalFabius`; varying-input spline convergence
completed: integrated the signed rounder, unrestricted spline evaluator,
  general/canonical computability results, moving-input estimate, and diagonal
  convergence; updated the README; drafted both TeX explanations, whose
  source snapshot pin and paired PDFs remain to be finalized
validated: direct elaboration and focused builds of `FabiusComputability` and
  `FabiusComputableSpline`; 4008-job facade build; facade-only
  `assert_no_sorry`, public-signature, and exact standard-axiom audit;
  executable sign/tie/zero examples; two independent read-only mathematics,
  API, and documentation reviews
next: commit the verified Lean/README batch, repin the walkthrough to that
  commit, update its source-module count, rebuild both PDFs three passes, and
  land the documentation batch
lease: acquired 2026-08-25T14:43:03-07:00; expires 2026-08-25T15:43:03-07:00
git owner / build owner: /root / /root
risks/questions: the unrestricted positive numerator controls a finite fold,
  so the result is a primitive-recursive correctness theorem rather than a
  practical complexity claim; denominator-zero behavior remains outside the
  rounder's correctness theorem
```

Source-only subagents inspect and prototype in `/tmp`; they do not edit the
leased production paths, run builds, or mutate Git state.
