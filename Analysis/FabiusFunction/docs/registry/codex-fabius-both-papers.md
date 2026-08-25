# Workstream registry: `codex/fabius-both-papers`

**Status: closed historical.** Both completed tranches entered `origin/main`
through exact tip `6fcbbb5da45330bdc78c6090706cf1479f3d3afb` and are incorporated by the
current theorem-refinements merge. The released lease below is provenance,
not live Git or build authority.

This file implements the per-branch registry fallback in
[`../COLLABORATION.md`](../COLLABORATION.md).

```text
SYNC Fabius
worktree/task: historical /root workstream — effective dyadic cumulant
  constants and a signed-global primitive-recursive spline evaluator
branch/base: codex/fabius-both-papers integrated into origin/main at
  6fcbbb5da45330bdc78c6090706cf1479f3d3afb
writing: none — both tranches complete
reading: historical only; no path lease is asserted by this record
expected API: pointwise `256/n` and `104448/n` normalized-moment estimates;
  an effective endpoint/Laplace logarithm comparison and explicit
  `2512945/(12n)` cumulant error for `n >= 224043`; signed-rational nearest
  rounding with half ties away from zero; a primitive-recursive signed-global
  spline evaluator with the same five-guard-unit error; general and canonical
  computability results; and moving-input spline convergence
completed: exposed the effective normalized-moment and endpoint/cumulant
  constants while retaining legacy asymptotic wrappers; added the signed
  rounder, unrestricted spline evaluator, general and canonical computability
  theorems, moving-input estimate, and diagonal convergence; updated the
  README, primary exposition, and Lean walkthrough
validated: the effective-constant tranche had focused builds for
  `LaplaceMomentBounds` and `FabiusDyadicSharpCumulant`, plus historical facade
  and audit evidence that predates later Lean changes. The signed-global
  tranche had direct elaboration, focused `FabiusComputability` and
  `FabiusComputableSpline` builds, a 4008-job facade build, facade no-sorry,
  public-signature, and standard-axiom audits, executable boundary examples,
  independent reviews, and three-pass builds of its 81-page primary exposition
  and 88-page walkthrough. These are component/historical results, not an
  exact-tree aggregate validation claim for the later 6fcbbb5d union
next: none — registry closed after integration
lease: released 2026-08-25T14:55:51-07:00
git owner / build owner: none / none (released historical lease)
risks/questions: retain `n >= 224043` exactly because it discharges the
  logarithm smallness condition; the unrestricted positive numerator controls
  a finite fold, so the signed-global result proves primitive-recursive
  correctness rather than a practical complexity bound; denominator-zero
  behavior remains outside the rounder's correctness theorem
```

Source-only subagents inspect and prototype in `/tmp`; they do not edit the
leased production paths, run builds, or mutate Git state.
