# Workstream registry: `codex/fabius-theorem-refinements`

**Status: active.** The exact source and build leases are recorded below.

This file is the durable cross-worktree record for the open-ended theorem,
refactoring, and documentation campaign on this branch.  Live task messages
supplement it but do not replace it.

```text
SYNC Fabius
worktree/task: c9a3 / root — theorem refinements and documentation
branch/base: codex/fabius-theorem-refinements at
  published checkpoint 23bfd95d04087eec63958e2b1e9b0c89d2e623e7,
  with pinned origin/main 35852aa65ba66cf700419c296a78460b02bb65b3
  resolved for the current merge checkpoint
git owner: root in this worktree
build owner: not held; incoming components carry focused historical evidence,
  but no build has been run on the exact 23bfd95d0 + 35852aa65 union.  Recheck
  and claim the host-wide lane before any focused or aggregate replay
source lease: refreshed 2026-08-25 13:54 -07:00 through 14:54 -07:00
next synchronization checkpoint: publish this pinned merge, re-fetch
  origin/main, and record whether the remote pin remained current; then pursue
  the exact combined-tree Lean replay under the single build owner
```

## Current integration and validation lease

- `Lean/FabiusFunction/FabiusQBinomialTaylor.lean`: the reviewed all-index
  coefficient, zero, natural-degree, degree, leading-coefficient, and boundary
  APIs, together with the redundant-`CharZero` cleanup, are published at
  `a95bd1913`; this lease is retained only for merge repair and the pending
  focused combined-tree build.
- `README.md`: the translated-polynomial documentation is published at
  `a95bd1913`; this merge also leases the inverse-branch prose corrections
  listed below.
- `docs/AUDIT_FINDINGS.md`: close the verified redundant-`CharZero` API
  finding.
- `docs/COLLABORATION.md`: retire the translated-polynomial candidate once the
  theorem batch is compiled and published.
- `docs/registry/codex-fabius-theorem-refinements.md`: this status record.
- Fifth integration lease for pinned main `35852aa65` over published checkpoint
  `23bfd95d0`: retain the incoming arbitrary Bose cutoffs, nonvanishing-base
  variable-power closure, scalar/all-index q-binomial APIs, all-order inverse
  endpoint steepness, continuous-linear saddle transport, exact Fourier
  samples, saddle-kernel real structure, and real-ray periodic Laplace bound.
  Preserve the branch-only translated-polynomial coefficient/zero/degree API.
- Semantic artifact repair lease for this nontrivial merge:
  `docs/Non_Elementarity_of_the_Fabius_Function/Non_Elementarity_of_the_Fabius_Function.{tex,pdf}`,
  `docs/Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.{tex,pdf}`,
  `docs/non-formalized-research-frontiers/Rvachev_Up_from_Repeated_Integration-2/Rvachev_Up_from_Repeated_Integration.tex`,
  `docs/registry/claude-fabius-non-elementary-proof-861d70.md`, and this active
  registry.  This covers semantic conflict resolution, stale-reference repair,
  explicit formalization boundaries, reproducible PDF rebuilds, and immutable
  validation attribution.

## Read-only survey

- `ThueMorsePrefix.lean`, `ThueMorseExponential.lean`,
  `ThueMorseGenerating.lean`, and `FabiusUniformSpline.lean` for existing
  sharp-moment and real-scalar APIs;
- `ProbabilityLaplaceMoments.lean`, `FabiusComplexMGF.lean`, and their callers
  to avoid reintroducing transform bridges already integrated upstream; and
- `AlgebraicBranch.lean` and `NotElementary.lean`, whose completed localized
  algebraic-branch implementation is integrated at `0f1a20a7c` and whose
  historical registry was closed at `3de52ca1c`, to avoid duplicating that
  theorem family; and
- current branch registry files and advertised remote tips before expanding
  either write set.

## Completed and published checkpoints

- `b49741f22`: exact affine sharp-degree Thue--Morse moment and consumer
  refactors; its equivalent mainline form is now integrated upstream.
- `44bdcbd8e`: canonical real-input complex generating bridge with a deprecated
  compatibility alias and migrated callers; the resulting API is now also on
  mainline.
- `1567c96b4`: all-real probability/support documentation and repaired paper
  entry points.
- `09885a710`: one operational coordination authority, immutable synchronization
  pins, direct-main authorization boundaries, and explicit feedback routes.
- `fdae28cab` on mainline now supplies the arbitrary-complex MGF derivative
  bound and keeps the vertical-line theorem as a compatibility wrapper, so the
  provisional transform candidate on this branch is retired.
- `a049141fb` on mainline supplies the unified rational affine and translated
  power-sum API; the distinct formal-polynomial coefficient/zero/degree batch
  remains open and should build on those names.
- `0f1a20a7c` on mainline integrates the localized algebraic-branch
  implementation, including the direct nowhere-analytic corollaries;
  `3de52ca1c` closes its historical registry, so the formerly advertised work
  is no longer an open lane.
- `5e80805b1` on mainline integrates the foundational/Fourier/probability and
  finite-remainder generalizations.  In particular `cfc70e3bc` factors the
  q-binomial refinement coefficient argument by degree without consuming the
  separate translated-polynomial coefficient/zero/degree lane leased here.
- `a95bd1913` on this branch publishes the exact translated-polynomial
  coefficient, zero, degree, leading-coefficient, and boundary-normal-form API,
  plus the redundant-`CharZero` cleanup and matching README documentation.
- `ad6cf6a07` publishes the first pinned-main integration at `1e371c773`, with
  the translated-polynomial batch retained and its exact combined-tree Lean
  validation explicitly deferred.
- `4b8c0094e` publishes the second pinned-main integration at `639bfc53e`, with
  the right-inverse/interior-complement API resolved coherently, the
  non-elementarity paper rebuilt and inspected, and exact combined-tree Lean
  validation explicitly deferred behind the then-active external build owner.
- `996ef2421` publishes the third pinned-main integration at `783cecf720`, with
  the core inverse calculus and conditional inverse-branch documentation
  reconciled, the non-elementarity paper rebuilt, and the new dyadic/q
  research-frontier article supplied with a rendered PDF.  Its exact combined
  Lean replay was explicitly deferred.
- `23bfd95d0` publishes the fourth pinned-main integration at `a24af8347`, with
  exact inverse smoothness, all-order flat-remainder and vector-valued
  small-argument APIs retained, three documentation artifacts rebuilt and
  inspected, and exact combined-tree Lean validation explicitly deferred.

Each substantive non-merge checkpoint message records its exact textual
validation and any deferred Lean targets.  Incoming commits `b164f3d2f` and
`c62a56d95` report focused and aggregate validation of the core inverse
calculus and smoothness, while the other incoming mathematical lanes likewise
carry focused immutable evidence.  Those reports predate the current-only
translated-polynomial batch and do not validate the exact combined
`23bfd95d0 + 35852aa65` tree.

## Current merge-checkpoint evidence

This checkpoint merges exact incoming tip
`35852aa65ba66cf700419c296a78460b02bb65b3` into exact published branch
checkpoint `23bfd95d04087eec63958e2b1e9b0c89d2e623e7`.  The merge base is
`a24af8347aba5d38b8febf2cf9a19eeef6aba18a`; the sides were 12 and 28
commits ahead of that base.  Git reported six conflict paths: two Lean
docstrings, the primary synthesis source, the non-elementarity source/PDF
pair, and the closed non-elementarity registry.

The incoming range changes 26 Lean modules and adds 23 public declarations
plus one private helper without removing or weakening a public declaration.
All 26 files retain `set_option autoImplicit false`.  The new APIs cover
arbitrary Bose cutoffs, nonvanishing-base real powers, scalar/all-index
q-binomial coefficients, all-order inverse endpoint steepness,
continuous-linear transport of asymptotic expansions, normalized saddle
kernel components, integer Fourier samples, and a real-ray periodic
negative-Laplace estimate.  The two textual Lean conflicts changed
documentation only; their resolution preserves the exact pointwise
positivity, nonvanishing, totalization, right-inverse, and complementary-
interior analyticity hypotheses.

The primary synthesis was rebuilt from the incoming structural rewrite rather
than either stale parent artifact.  The resolution defines the Lean-name macro
in both text and math mode; repairs nine dangling references, one duplicate
label, and six nonexistent module paths; restores the exact normalized-moment
and Thue--Morse recurrences; and replaces the incoming unformalized
mass-to-log coefficient and numerical passages with the proved top-mass-jet
theorem.  The omitted conventional material remains preserved in
`docs/non-formalized-research-frontiers/Small_Argument_Asymptotics/`.

Both conflicted papers received three successful PDFLaTeX passes and
representative rendered-page inspection:

- the primary synthesis is 75 A4 pages, with 468 unique labels, 455 resolved
  reference uses, and PDF SHA-256
  `2B86AD8AF5FC370350B13947CA6394923F7FA17349589019816250CF56CB0D05`;
- the non-elementarity paper is 14 A4 pages, with 23 unique labels, 91
  resolved reference uses, and PDF SHA-256
  `AB722E11F7B72916CA079CC3FFF8BCD1B3CA7B68D104DCF8FF3853FB04C777E1`.

The final logs contain no undefined references or citations, multiply defined
labels, rerun notices, fatal errors, or overfull boxes.  The primary log has
only harmless PDF-bookmark token warnings and one underfull box; the
non-elementarity log has three underfull-box diagnostics.  The added
repeated-integration frontier source also has its sole trailing-space defect
repaired without changing rendered content.

The three imported frontier TeX/PDF pairs are retained as incoming historical
artifacts, not claimed formal results.  Their overlapping dyadic-asymptotic and
repeated-integration scopes, mutable provenance in two drafts, uneven
first-page boundary notices, and the parallel `-2` directory need a separately
leased consolidation; no canonical-source claim or live ownership is granted
by this merge.

Post-resolution static gates are clean: `git diff --cached --check`, the
tree-wide conflict-marker and forbidden declaration/placeholder scans, all 188
Lean modules carrying `set_option autoImplicit false`, 46 local Markdown links,
and all 15 project-authored TeX/PDF pairs.  The documentation ratchet passes at
188 modules, 3,181 public declarations, 156 pre-existing undocumented
declarations in 17 files, and zero missing module headers.

Incoming components carry focused immutable build evidence, and
`c6e2da733` records a 35-module non-elementarity closure build plus a
105-declaration standard-axiom sweep.  Neither the exact incoming union nor
this manually resolved union has an exact aggregate Lean build.  The focused
q dependency chain, umbrella target, and axiom audit remain pending until the
host-wide single build lane is checked and claimed.

## Reviewed translated-polynomial API

Independent mathematical/API review and a separate hostile source preflight
confirmed the following coherent declaration family:

- an exact coefficient formula in terms of
  `thueMorseCenteredPowerSum k (d - j)`;
- vanishing exactly when `d < k`; and
- the all-index degree drop `natDegree = d - k`, the exact `WithBot`-valued
  degree and leading coefficient, and the `k = 0` and `d = k` normal forms.

The reviews checked `k = d = 0`, `k = 0`, `d < k`, `d = k`, `j > d`, the
nonzero leading coefficient, simp critical pairs, and the four redundant
`CharZero` binders.  The hostile preflight found and repaired one associativity
mismatch in the sharp-coefficient nonzero proof, then found no remaining
source-level blocker against the exact Mathlib signatures and import closure.
On the pre-merge `a95bd1913` tree, `git diff --check`, the
forbidden-placeholder/conflict-marker scans, and the documentation baseline
gate passed.  The fifth pinned integration at `35852aa65` is source-resolved
over published checkpoint `23bfd95d0`; active ownership is unchanged, and
focused Lean validation of the exact combined tree remains pending until this
merge is published and the host-wide build lane is rechecked and claimed.
