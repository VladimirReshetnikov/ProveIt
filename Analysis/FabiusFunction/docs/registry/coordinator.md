# Fabius campaign coordinator board

This is the canonical repository-visible control plane for concurrent work in
`Analysis/FabiusFunction`.  Only the designated coordinator edits this file.
Every worker reads it from the fetched `origin/main` before writing, merging,
building, or pushing.  Workers publish replies in their own per-branch registry
files; they do not edit this board.

## Checkpoint 2026-08-26 03:49 PDT

```text
observed main before this directive: 44517be3cd72257f6d3dbdfdc8293279387b96aa
coordinator branch: codex/fabius-coordinator-20260825
integration mode: exact immutable sources -> coordinator -> fast-forward main
main write owner: coordinator
codexbox Lean/Lake owner: unassigned
  (IDLE after the green three-gate sequence below)
codexbox TeX/PDF owner: unassigned
  (IDLE)
EVO Lean/Lake owner: codex/fabius-inverse-asymptotic-20260825
  (ACTIVE: the disjoint decay proof-repair retry)
EVO TeX/PDF owner: unassigned
  (IDLE)
documentation owner: unassigned
  (all canonical documents are frozen)
next poll: at the EVO decay handoff or next immutable source handoff
```

**Zero-inclusive endpoint comparisons and Thue--Morse core cleanup accepted.**
Exact reviewed sources were mapped as coordinator commits `8e504ad83` and
`20f63650a`.  Final candidate
`20f63650a55aa2bbb03329edfb6653c23a4f3063`, tree
`e3170070880e272e55ab8f19c2f54167305ac8a8`, contains precisely the three
advertised result blobs and no feature-registry/history import.

On codexbox, with no overlapping Lean/Lake/TeX process, the three separate
commands from the grant ran in order under `LEAN_NUM_THREADS=0 LAKE_JOBS=1`:

```text
+FabiusFunction.EndpointLaplaceComparison  3417 jobs, exit 0
+FabiusFunction.ThueMorsePrefix             2025 jobs, exit 0
+FabiusFunction.ThueMorseGenerating         2088 jobs, exit 0
```

The endpoint command emitted only the inherited
`ProbabilityLaplaceMoments.lean:652:2` `unnecessarySimpa` linter.  Both
Thue--Morse commands emitted no diagnostic.  No proof repair was needed.  The
eight additive all-index endpoint declarations, strict 24/24 documentation,
the exact private-helper replacement, and strict 27/27 plus 47/47
documentation are accepted.  Every source path and the codexbox token are
released.  No consumer/root/document gate is required for these additive or
header-preserving units.  The Bose cutoff and Rvachev evaluator lanes remain
outside this acceptance pending their own immutable-source dispositions.

## Checkpoint 2026-08-26 03:46 PDT

```text
observed main before this directive: 65df99318029015fc04b971c439dc754f2ef7dd6
coordinator branch: codex/fabius-coordinator-20260825
integration mode: exact immutable sources -> coordinator -> fast-forward main
main write owner: coordinator
codexbox Lean/Lake owner: coordinator
  (ACTIVE: exactly the three serialized gates below)
codexbox TeX/PDF owner: unassigned
  (IDLE)
EVO Lean/Lake owner: codex/fabius-inverse-asymptotic-20260825
  (ACTIVE: the disjoint decay proof-repair retry)
EVO TeX/PDF owner: unassigned
  (IDLE)
documentation owner: unassigned
  (all canonical documents are frozen)
next poll: after each codexbox gate and at the EVO decay handoff
```

**Codexbox validation batch: zero-inclusive endpoint comparisons and
Thue--Morse core-bound cleanup.**  Two path-disjoint immutable source units
have exact current-main preimages and independent actual-diff static PASSes:

- `0409c13d1` changes only `EndpointLaplaceComparison.lean` to blob
  `e7170713a4c8fd4993009cba9cc0786cd7b72161`.  It adds exactly eight
  documented zero-inclusive `_all` declarations, preserves all 16 old
  declarations/imports/bodies and every attribute, and yields strict 24/24
  public documentation.  The zero/positive splits, all-real mass positivity,
  and totalized logarithmic zero case were reviewed without a collision.
- `44b2352a8baefed1f54106d9338eac8d931f4f78` changes only
  `ThueMorsePrefix.lean` and `ThueMorseGenerating.lean` to blobs
  `fcbb7d08ba52974c069cf389db8d2460378dbb7b` and
  `fb403c24606b0091aead89de26bb6b0f9dde2f97`.  It deletes two private power
  bounds, replaces their four uses with `Nat.lt_two_pow_self` in the exact
  weak/strict orientations, changes Generating only by comments, preserves
  every public header/import/attribute, and completes strict 27/27 and 47/47
  documentation.

Neither unit has compiler evidence.  Integrate only these exact source commits
and blobs, never the moving effective-bounds feature history.  On codexbox run
exactly the following separate commands, in order, with strict
stop-on-first-failure:

```text
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.EndpointLaplaceComparison
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.ThueMorsePrefix
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.ThueMorseGenerating
```

Run no parallel or additional codexbox Lean/Lake/TeX/PDF process.  Record the
exact candidate/tree, each job count, exit, and every diagnostic.  Only an
independently reviewed statement-preserving proof repair is in scope after a
failure.  The simultaneous EVO decay retry remains independent on its other
physical host.  The new Bose cutoff and Rvachev rational-evaluator requests
are outside this grant; neither receives a source or build token here.

## Checkpoint 2026-08-26 03:41 PDT

```text
observed main before this directive: e35baa1fcf4ade15dff67dad624002c527fd9fd3
coordinator branch: codex/fabius-coordinator-20260825
integration mode: exact immutable sources -> coordinator -> fast-forward main
main write owner: coordinator
codexbox Lean/Lake owner: unassigned
  (IDLE after the green six-gate sequence below)
codexbox TeX/PDF owner: unassigned
  (IDLE)
EVO Lean/Lake owner: codex/fabius-inverse-asymptotic-20260825
  (ACTIVE: the disjoint decay proof-repair retry)
EVO TeX/PDF owner: unassigned
  (IDLE)
documentation owner: unassigned
  (all canonical documents are frozen)
next poll: at the EVO decay handoff or next immutable source claim
```

**Gaussian-contraction consolidation and exp-minus-one shift bounds
accepted.**  Exact reviewed sources were mapped as coordinator commits
`c2861fa0c` and `8f0f443b7`.  Final candidate
`8f0f443b72cc2c01becf810801153cd4a3a758f5`, tree
`63facc1d42e776e78d098650293b43af3add303a`, contains precisely the five
advertised result blobs and no feature-registry/history import.  The source
provenance correction is binding: the accepted exp-shift source is actual
commit `a1c417019215d629e6c389c05bfd111ab5c09f7a`, not the nonexistent full SHA
printed in its branch handoff.

On codexbox, with no overlapping Lean/Lake/TeX process, the six separate
commands from the grant ran in order under `LEAN_NUM_THREADS=0 LAKE_JOBS=1`:

```text
+FabiusFunction.GaussianPolynomialContraction          2868 jobs, exit 0
+FabiusFunction.FabiusSaddleExpansionCoefficients      3309 jobs, exit 0
+FabiusFunction.FabiusSecondSaddleCorrection           3312 jobs, exit 0
+FabiusFunction.FabiusDiscreteLimitComplexShift        1873 jobs, exit 0
+FabiusFunction.FabiusComplexShiftSpline               3421 jobs, exit 0
+FabiusFunction.FabiusDiscreteLimitIntegration         3427 jobs, exit 0
```

The first three commands emitted no diagnostic.  The fourth emitted one
nonblocking `unnecessarySimpa` linter at
`FabiusDiscreteLimitComplexShift.lean:335:8`; the fifth and sixth only replayed
that same upstream linter.  No proof repair was needed.  Both source units,
the public scalar-monomial contraction theorem and private deduplication, all
four shift bounds, preserved compatibility APIs, and the two direct-consumer
closures are accepted.  Every source path and the codexbox token are released.
The registry-only zero-inclusive endpoint claim remains unimplemented and has
no source or build grant.  No document path is released or activated by this
source acceptance.

## Checkpoint 2026-08-26 03:38 PDT

```text
observed main before this directive: f8464b2d4a2aa250d716dabbb435d269c759bba9
coordinator branch: codex/fabius-coordinator-20260825
integration mode: exact immutable sources -> coordinator -> fast-forward main
main write owner: coordinator
codexbox Lean/Lake owner: coordinator
  (ACTIVE: exactly the six serialized gates below)
codexbox TeX/PDF owner: unassigned
  (IDLE)
EVO Lean/Lake owner: codex/fabius-inverse-asymptotic-20260825
  (ACTIVE: the disjoint decay proof-repair retry)
EVO TeX/PDF owner: unassigned
  (IDLE)
documentation owner: unassigned
  (all canonical documents are frozen)
next poll: after each codexbox gate and at the EVO decay handoff
```

**Codexbox validation batch: Gaussian-contraction helper consolidation and
exp-minus-one complex-shift bounds.**  Two path-disjoint immutable source
units have exact current-main preimages and independent hostile static PASSes:

- `8f0dbf7eae03a096368a9afc00d8139b7cf79f19` changes only
  `GaussianPolynomialContraction.lean`,
  `FabiusSaddleExpansionCoefficients.lean`, and
  `FabiusSecondSaddleCorrection.lean`, to blobs
  `6e466f4ea2bf325e33980376400dba50eb8fec6e`,
  `9e5d94a7cf6016935a373c7677076b97dbd81cb4`, and
  `c9a762985186e06030d789b1774ac01af8f3fa76`.  It exposes the reviewed
  scalar-monomial Gaussian-contraction simp theorem, deletes two private
  duplicates, rewires all six consumers, preserves imports and old public
  headers, and completes the advertised declaration comments.
- The exp-shift handoff abbreviates its source correctly as `a1c417019` but
  records a nonexistent full SHA.  The actual immutable source is
  `a1c417019215d629e6c389c05bfd111ab5c09f7a`; only that commit is accepted for
  validation.  It changes `FabiusDiscreteLimitComplexShift.lean` and
  `FabiusComplexShiftSpline.lean` to blobs
  `c12704bab4fe31bbf9580f519e99e07b56814733` and
  `4b687921f5dd7ba586d1a10ac75355874aa5e644`, adding four reviewed public
  exp-minus-one bounds while preserving all six legacy plain-exponential
  headers, imports, attributes, and boundary cases.

Neither unit has compiler evidence.  Integrate only these exact source
commits/blobs, never either moving feature history.  On codexbox run exactly
the following separate commands, in order, with strict stop-on-first-failure:

```text
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.GaussianPolynomialContraction
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.FabiusSaddleExpansionCoefficients
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.FabiusSecondSaddleCorrection
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.FabiusDiscreteLimitComplexShift
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.FabiusComplexShiftSpline
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.FabiusDiscreteLimitIntegration
```

Run no parallel or additional codexbox Lean/Lake/TeX/PDF process.  Record the
exact candidate/tree, each job count, exit, and every diagnostic.  Only an
independently reviewed statement-preserving proof repair is in scope after a
failure.  The simultaneous EVO decay retry remains independent on its other
physical host.  The zero-inclusive endpoint comparison request remains a
registry-only design claim and receives no source lease or build token here.

## Checkpoint 2026-08-26 03:27 PDT

```text
observed main before this directive: ed8d996b78e9858d1282c7c5622c9b4ac61796da
coordinator branch: codex/fabius-coordinator-20260825
integration mode: exact immutable sources -> coordinator -> fast-forward main
main write owner: coordinator
codexbox Lean/Lake owner: unassigned
  (IDLE after the green eight-gate sequence below)
codexbox TeX/PDF owner: unassigned
  (IDLE)
EVO Lean/Lake owner: codex/fabius-inverse-asymptotic-20260825
  (ACTIVE: the disjoint decay proof-repair retry)
EVO TeX/PDF owner: unassigned
  (IDLE)
documentation owner: unassigned
  (all canonical documents are frozen)
next poll: at the EVO decay handoff or next immutable source claim
```

**Factorized tails, expCoeff extensionality, parity-power summability, and
probability-law deduplication accepted.**  Exact isolated sources were mapped
as coordinator commits `a7cc1611a`, `243ddbc8e`, `62e9fd672`, and
`0fc2bd48d`.  Final candidate `0fc2bd48d768a16593c8f89898c6dde9ead178de`,
tree `97eb774bd712f4db2dfde874992272e0b4a774e9`, contains precisely the five
reviewed result blobs and no feature-registry/history import.

On codexbox, with no overlapping Lean/Lake/TeX process, the eight separate
commands from the grant ran in order under
`LEAN_NUM_THREADS=0 LAKE_JOBS=1`:

```text
+FabiusFunction.FabiusSaddleTail             3199 jobs, exit 0
+FabiusFunction.FabiusLambertMinorArc        3263 jobs, exit 0
+FabiusFunction.SaddleExpansionAlgebra       2186 jobs, exit 0
+FabiusFunction.SaddleLogExpansionAlgebra    2187 jobs, exit 0
+FabiusFunction.FabiusParityPowerSeries      3251 jobs, exit 0
+FabiusFunction.PaperFabiusAsymptotic        3964 jobs, exit 0
+FabiusFunction.ProbabilityRepresentation    3131 jobs, exit 0
+FabiusFunction.FabiusUniformSpline          3419 jobs, exit 0
```

Seven commands emitted no diagnostic.  `PaperFabiusAsymptotic` emitted only
the inherited `ProbabilityLaplaceMoments.lean` unnecessary-`simpa` linter.
No proof repair was needed.  All four units, their preserved wrappers/rewires,
the completed declaration comments, and the two direct-consumer closures are
accepted.  Every source path and the codexbox token are released.  Proposed
frontier and audit-ledger follow-ups remain separate frozen documentation
work; this source acceptance grants no document path.

## Checkpoint 2026-08-26 03:17 PDT

```text
observed main before this directive: 59fd2f0a42045547be8aa00070dd94fdb4ab7119
coordinator branch: codex/fabius-coordinator-20260825
integration mode: exact immutable sources -> coordinator -> fast-forward main
main write owner: coordinator
codexbox Lean/Lake owner: coordinator
  (ACTIVE: exactly the eight serialized gates below)
codexbox TeX/PDF owner: unassigned
  (IDLE)
EVO Lean/Lake owner: codex/fabius-inverse-asymptotic-20260825
  (ACTIVE: the disjoint decay proof-repair retry)
EVO TeX/PDF owner: unassigned
  (IDLE)
documentation owner: unassigned
  (all canonical documents are frozen)
next poll: after each codexbox gate and at the EVO decay handoff
```

**Codexbox validation batch: factorized tails, expCoeff extensionality,
parity-power summability, and probability-law deduplication.**  Four isolated
sources have exact current-main preimages and independent static PASSes:

- `bbaed0ee6d25d8026a848338c8f47ff967d2a90b` changes only
  `FabiusSaddleTail.lean` to blob
  `9712b7a684aa82e21bc0f1a3ff5f533d1eba7fc5`, adding the factorized Big-O
  theorem, preserving the old wrapper header, and completing 30/30 docs;
- `60e6339404f7b5fd387b43f56c6fdbd8e1d5f01a` changes
  `SaddleExpansionAlgebra.lean` to blob
  `06febd7843297461eea08451198620e269a47805` and
  `SaddleLogExpansionAlgebra.lean` to
  `dc8ed947850a5a45e49c260d8cb0a83390f089f9`, exposing the reviewed
  positive-index `expCoeff_eq_of_forall_pos` and deleting its local reproof;
- `5ed786a92dfebeaf158def6089da73ad107834b5` changes only
  `FabiusParityPowerSeries.lean` to
  `a5ba001cc339c840108f21d9bfbc85ee7a8a7361`, adding all-real absolute
  summability plus the exact nonnegative compatibility wrapper; and
- `447ba3be09a20c8988edeb98f7430133f93b1f1e` changes only
  `ProbabilityRepresentation.lean` to
  `aefd5cb38a5cf6e719f532dc1cc88f3e2992ba6d`, byte-preserving and hoisting
  the two coordinate-law declarations and replacing four reconstructions.

All theorem directions, constants, filters, edge cases, imports, existing
headers/attributes, rewires, comments, and collision scans pass.  No unit has
compiler evidence yet.  Integrate only these exact commits/blobs, never either
moving feature history.  On codexbox run exactly the following separate
commands, in order, with strict stop-on-first-failure:

```text
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.FabiusSaddleTail
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.FabiusLambertMinorArc
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.SaddleExpansionAlgebra
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.SaddleLogExpansionAlgebra
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.FabiusParityPowerSeries
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.PaperFabiusAsymptotic
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.ProbabilityRepresentation
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.FabiusUniformSpline
```

Run no parallel or additional codexbox Lean/Lake/TeX/PDF process.  Record the
exact candidate/tree, each job count, exit, and every diagnostic.  Only a
reviewed statement-preserving proof repair is in scope after failure.  The
simultaneous EVO retry remains independent on its different physical host.

## Checkpoint 2026-08-26 03:11 PDT

```text
observed main before this directive: 6691afcb39f5a50dbc0d798b8b75b4cf563bf50a
coordinator branch: codex/fabius-coordinator-20260825
integration mode: exact immutable sources -> coordinator -> fast-forward main
main write owner: coordinator
codexbox Lean/Lake owner: unassigned
  (IDLE)
codexbox TeX/PDF owner: unassigned
  (IDLE)
EVO Lean/Lake owner: codex/fabius-inverse-asymptotic-20260825
  (ACTIVE: exact decay proof repair plus the three-gate retry below)
EVO TeX/PDF owner: unassigned
  (IDLE)
documentation owner: unassigned
  (all canonical documents are frozen)
next poll: at the repaired decay validation handoff or first failed retry gate
```

**Inverse-power decay failure accepted; exact proof repair and retry granted.**
Validation tree `2ad7703d374d42a6f451b28a49c3f12c64ced99e`
retained exact source blob `5a407fe366bead3fa2bb8f9d90cac14900fc46bf`.
On EVO, the first granted command used strict one-child serialization,
scheduled 3,312 jobs, reached `FabiusDecayComparison`, and exited 1 with
exactly two target-local normalization diagnostics.  The worker correctly
skipped both consumer gates, changed no source or cache, recorded failure in
`7e215ae3e`, released the token, and synchronized current main at clean tip
`95bbca7c5` with the source blob unchanged.

Independent review confirms both failures are proof-normalization only.  Grant
that branch sole ownership of exactly
`Lean/FabiusFunction/FabiusDecayComparison.lean` and its own registry for only
these two edits:

1. Immediately before the existing `Real.rpow_def_of_pos` rewrite in the
   second `congr'` branch, beta-reduce the displayed lambdas with
   `change Real.exp (Real.log 2 * β * t) = (2 : ℝ) ^ (β * t)`;
   retain the existing rewrite, `congr 1`, and `ring`.
2. Change only `simpa only [Function.comp_def]` in the positive-rate Tendsto
   proof to `simpa only [Function.comp_def, id_eq]`.

No declaration name/header/hypothesis, import, module prose, other proof, or
other path may change.  Commit and push the repaired source, verify that its
diff from blob `5a407fe366` is exactly those normalizations, and record the new
blob/hash in the branch registry.  Then, without a second micro-grant, use
EVO's sole Lean/Lake token to rerun from the first target as these three
separate commands in order, stopping after the first nonzero exit:

```text
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.FabiusDecayComparison
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.FabiusQuotientExponentialMismatch
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.PaperKFoldThueMorse
```

No fourth/root/facade target, parallel process, cache clean/reconstruction,
TeX/PDF, canonical document, or main write is authorized.  Record exact repair
commit/tree/blob, commands, job counts, exits, and every diagnostic; push only
the feature branch and release the EVO token at the handoff.

## Checkpoint 2026-08-26 03:07 PDT

```text
observed main before this directive: ec20ebdeb8e9ff74bcaa0534317332a408deea1a
coordinator branch: codex/fabius-coordinator-20260825
integration mode: exact immutable sources -> coordinator -> fast-forward main
main write owner: coordinator
codexbox Lean/Lake owner: unassigned
  (IDLE)
codexbox TeX/PDF owner: unassigned
  (IDLE)
EVO Lean/Lake owner: codex/fabius-inverse-asymptotic-20260825
  (ACTIVE: the inverse-power decay sequence)
EVO TeX/PDF owner: unassigned
  (IDLE)
documentation owner: unassigned
  (all canonical documents are frozen)
next poll: at an immutable SaddleTail source handoff or the EVO decay handoff
```

**Effective-bounds SaddleTail claim accepted without a build token.**
Registry-only commit `0105b4a0b9e4e69057fd2cab93da746843b0efb3`
reserves exactly `Lean/FabiusFunction/FabiusSaddleTail.lean` and the branch's
own registry.  Current source remains exact blob
`5f70fc0e17832fc5e5c0412b7c9369c9ee400a6d`; no implementation or compiler
evidence exists yet.

The proposed public theorem
`integral_norm_fabius_scaledSaddleKernel_standardRadius_isBigO_minorArcConstant_mul_inv`
is mathematically/API-sound: the existing pointwise bound already gives
`tail_i <= C_i * ((16 + 32*pi) * b_i^-1)` from eventual positivity,
`16 <= b_i`, and `b_i / 4 <= m_i`, without requiring `b -> infinity` or
`C = O(1)`.  The existing public `O(1/b)` theorem must retain its exact header
and become a compatibility consequence.  The bounded source scope also adds
the reviewed module sentence and comments for the 17 currently undocumented
public declarations; it changes no import, facade, root, or document path.

Permit ordinary source authoring under that exact one-file reservation.  Do
not grant or run a build until an immutable source/handoff receives actual-diff
review.  The later minimal serialized gates are
`+FabiusFunction.FabiusSaddleTail`, then its exact compatibility consumer
`+FabiusFunction.FabiusLambertMinorArc`, both with the repository-prescribed
serialization controls.  No broader facade gate is reserved.

## Checkpoint 2026-08-26 03:06 PDT

```text
observed main before this directive: d545ecf73bc925881b9ff97e81c318ee33407ade
coordinator branch: codex/fabius-coordinator-20260825
integration mode: exact immutable sources -> coordinator -> fast-forward main
main write owner: coordinator
codexbox Lean/Lake owner: unassigned
  (IDLE after the green six-gate sequence below)
codexbox TeX/PDF owner: unassigned
  (IDLE)
EVO Lean/Lake owner: codex/fabius-inverse-asymptotic-20260825
  (ACTIVE: the disjoint inverse-power decay sequence)
EVO TeX/PDF owner: unassigned
  (IDLE)
documentation owner: unassigned
  (all canonical documents are frozen)
next poll: at the EVO decay handoff or next immutable source claim
```

**Periodic reassembly/documentation and inverse endpoint-filter promotion
accepted.**  The six exact reviewed path results were mapped as coordinator
commit `ab2648e47057faa6aeb99b89f57fdc29a75bade4`, tree
`477f2f2155cff5516572d0cd81efee00149d2f00`.  No moving feature history or
registry was merged.  On codexbox, with no overlapping Lean/Lake/TeX process,
the six granted commands ran separately in order under
`LEAN_NUM_THREADS=0 LAKE_JOBS=1`:

```text
+FabiusFunction.PeriodicMean                3272 jobs, exit 0
+FabiusFunction.PeriodicRegularity          3298 jobs, exit 0
+FabiusFunction.PeriodicFourier             3663 jobs, exit 0
+FabiusFunction.PeriodicSmooth              3300 jobs, exit 0
+FabiusFunction.FabiusInverse               3252 jobs, exit 0
+FabiusFunction.FabiusInverseAsymptotic     3935 jobs, exit 0
```

The first five commands emitted no diagnostic.  The final command emitted
only the inherited `ProbabilityLaplaceMoments.lean` unnecessary-`simpa`
linter already recorded by prior hierarchy gates.  No proof repair was
needed.  The three generic dyadic reassembly theorems and five rewires, both
complete periodic declaration inventories, the promoted endpoint-filter
transport, and the deduplicated repaired inverse hierarchy are accepted.
All six source paths and the codexbox token are released.

## Checkpoint 2026-08-26 02:56 PDT

```text
observed main before this directive: 7cfc103ff85b73070625f0556652442af7819c14
coordinator branch: codex/fabius-coordinator-20260825
integration mode: exact immutable sources -> coordinator -> fast-forward main
main write owner: coordinator
codexbox Lean/Lake owner: coordinator
  (ACTIVE: exactly the six effective-bounds gates below)
codexbox TeX/PDF owner: unassigned
  (IDLE)
EVO Lean/Lake owner: codex/fabius-inverse-asymptotic-20260825
  (ACTIVE: the disjoint inverse-power decay sequence)
EVO TeX/PDF owner: unassigned
  (IDLE)
documentation owner: unassigned
  (all canonical documents are frozen)
next poll: after each codexbox gate and at the EVO decay handoff
```

**Codexbox validation batch: periodic reassembly/documentation and inverse
endpoint-filter promotion.**  Static review accepts four selective
effective-bounds tranches, while explicitly rejecting the moving feature
history as an integration base.  Exact combined source tree
`7dbd08b2242f9f6cc2906aec45de727442ee780f` supplies only these six result
blobs against byte-identical current-main preimages:

- `PeriodicMean.lean` `9a0e290cbd999cd9a3aa3ff92fc23acd2ac8ffdc`;
- `PeriodicFourier.lean` `21bb543f682d0beb48bf6ea2fc69bc9b9f94c873`;
- `PeriodicRegularity.lean` `394e2ba61edb76f65c44e90fd722c6f448b56253`;
- `PeriodicSmooth.lean` `f09e73b35accd3d426fea843eb2122ad5b214df9`;
- `FabiusInverse.lean` `38774772f11a2c084d3c2e5189d3f632da941154`;
- repaired `FabiusInverseAsymptotic.lean`
  `c53f208845552ebceffa3e3be4d569fc06947282`.

The first pair adds the three reviewed generic dyadic reassembly `HasSum`
APIs and rewires their five consumers.  The two regularity files are
comment-only declaration-inventory completions with byte-identical
non-comment streams.  The inverse pair promotes the compiled endpoint-filter
transport into `FabiusInverse` and deletes its now-duplicate private endpoint
copy while preserving every repaired hierarchy theorem.  Imports and public
headers are unchanged and acyclic; exact/semantic scans are collision-free.
No item has compiler evidence in this combined tree yet.

Map only these exact six paths to the coordinator candidate.  On codexbox,
run from the repository root exactly the following separate commands, in
order, with strict stop-on-first-failure:

```text
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.PeriodicMean
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.PeriodicRegularity
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.PeriodicFourier
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.PeriodicSmooth
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.FabiusInverse
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.FabiusInverseAsymptotic
```

Run no parallel or additional codexbox Lean/Lake/TeX/PDF process.  Record the
exact candidate/tree, each command's job count, exit, and every diagnostic.
Only statement-preserving proof repair is in scope after a reviewed failure.
The simultaneous EVO sequence remains independent on its different host.

## Checkpoint 2026-08-26 02:54 PDT

```text
observed main before this directive: c7dfc250fe42bf66a241b59e1fa11eb5dd340d0f
coordinator branch: codex/fabius-coordinator-20260825
integration mode: exact immutable sources -> coordinator -> fast-forward main
main write owner: coordinator
codexbox Lean/Lake owner: unassigned
  (IDLE after the green six-gate sequence below)
codexbox TeX/PDF owner: unassigned
  (IDLE)
EVO Lean/Lake owner: codex/fabius-inverse-asymptotic-20260825
  (ACTIVE: the disjoint inverse-power decay sequence)
EVO TeX/PDF owner: unassigned
  (IDLE)
documentation owner: unassigned
  (all canonical documents are frozen)
next poll: at the EVO decay handoff or next immutable source claim
```

**Radial order, sparse Pascal parity, and shared binomial square accepted.**
The exact isolated sources from the prior checkpoint were mapped to the
coordinator as `6582311ae`, `84a84f5ef`, and `7e0c154fe`, respectively.
Candidate commit `84a84f5effc43bf9b81b92ec34e6ed8b9fa89ba6`, tree
`195ace0b9ad2222a394e066016f4a9698c1bd0dc`, has exactly the reviewed result
blobs on `Monotonicity.lean`, `Parity.lean`, `Arithmetic.lean`,
`HalfQBinomial.lean`, and `FabiusQBinomialFormula.lean`.

On codexbox, with no overlapping Lean/Lake/TeX process, the six separate
commands from the grant ran in order with `LEAN_NUM_THREADS=0` and
`LAKE_JOBS=1`:

```text
+FabiusFunction.Arithmetic                 1053 jobs, exit 0
+FabiusFunction.HalfQBinomial              2026 jobs, exit 0
+FabiusFunction.FabiusQBinomialFormula     3321 jobs, exit 0
+FabiusFunction.Monotonicity               2659 jobs, exit 0
+FabiusFunction.Parity                     1587 jobs, exit 0
+FabiusFunction.Paper06487                 3248 jobs, exit 0
```

No command emitted a warning or other diagnostic, and no proof repair was
needed.  The promoted `choose_square_split`, all three radial-ordering names,
both sparse-Pascal names, their compatibility rewires, and the paper facade
are accepted.  Every source path and the codexbox token are released.  The
historical triangular-number prose in `docs/AUDIT_FINDINGS.md` remains a
separate ledger-only cleanup; it was not changed or claimed by this source
batch.

## Checkpoint 2026-08-26 02:48 PDT

```text
observed main before this directive: 0f9a6db8313d626c52dc0e4ef31b42158bbd1bb0
coordinator branch: codex/fabius-coordinator-20260825
integration mode: exact immutable sources -> coordinator -> fast-forward main
main write owner: coordinator
codexbox Lean/Lake owner: coordinator
  (ACTIVE: exactly the six serialized gates below)
codexbox TeX/PDF owner: unassigned
  (IDLE)
EVO Lean/Lake owner: codex/fabius-inverse-asymptotic-20260825
  (ACTIVE: the disjoint inverse-power decay sequence in the prior checkpoint)
EVO TeX/PDF owner: unassigned
  (IDLE)
documentation owner: unassigned
  (all canonical documents are frozen)
next poll: after each codexbox gate and at the EVO decay handoff
```

**Codexbox validation batch: radial order, sparse Pascal parity, and shared
binomial square.**  Three path-disjoint immutable sources have independent
static PASSes and exact current-main preimages:

- radial ordering source `3463c9cb4ceaf1988c05e65954eefe1e350a91d5`
  changes only `Monotonicity.lean` to blob
  `aff1231e56d4c30bf40189c222c1c0fb8333e33c`, SHA-256
  `021F5A034C32577673E45A8E9C2474AC13FACB10EE7D79A0D7BB59F6D4B0C66A`;
- sparse Pascal source `1992f0c1488b5fd5fb3a22c3ff769e6eb1346000`
  changes only `Parity.lean` to blob
  `92ca2ea3ad73cff04749709d5a142d3bd01ea270`, SHA-256
  `0D195658E07BDB6D90294F62B8FD2230F5E7EDE9D6C48C2859D5D881CE64C13E`;
- shared-square source `43e06524b1a65e36361f5ca1ce24b6ae71108e61`
  promotes `choose_square_split` in `Arithmetic.lean` and deletes/rewires the
  two private duplicates in `HalfQBinomial.lean` and
  `FabiusQBinomialFormula.lean`.  Final blobs are respectively
  `0cde6a592e6f495f518e3b7a0cb1ddc3b5ae33b1`,
  `fc3a7f96e306f72bf05b2a3bd7e715800a9a1631`, and
  `8031d4c1171790481bf94adc15bd812931d8ae06`.

The reviewed theorem statements, edge cases, signs, imports, existing public
headers, and call-site rewires are accepted statically; exact-name and
semantic scans find no collision.  No source has compiler evidence yet.
Integrate only the three isolated source commits above on the coordinator
candidate, never the moving both-papers history.  On codexbox, from the
repository root, run exactly these separate commands in order, stopping at
the first nonzero exit:

```text
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.Arithmetic
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.HalfQBinomial
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.FabiusQBinomialFormula
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.Monotonicity
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.Parity
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.Paper06487
```

Run no parallel or additional codexbox Lean/Lake/TeX/PDF process.  Record each
command, exact candidate commit/tree, scheduled-job count, exit, and every
diagnostic.  Statement-preserving proof repairs remain coordinator-owned and
must receive static review before a retry.  The simultaneous EVO sequence is
independent and may continue on its different physical host.

## Checkpoint 2026-08-26 02:40 PDT

```text
observed main before this directive: fec88296a38c5eff4058fdbc66a54f9d87ffed82
coordinator branch: codex/fabius-coordinator-20260825
integration mode: exact immutable sources -> coordinator -> fast-forward main
main write owner: coordinator
codexbox Lean/Lake owner: unassigned
  (IDLE)
codexbox TeX/PDF owner: unassigned
  (IDLE)
EVO Lean/Lake owner: codex/fabius-inverse-asymptotic-20260825
  (ACTIVE: exactly the three inverse-power decay gates below)
EVO TeX/PDF owner: unassigned
  (IDLE)
documentation owner: unassigned
  (all canonical documents are frozen)
next poll: at the decay branch's validation handoff or first failed gate
```

**Inverse-power decay validation grant.**  Immutable synchronized candidate
`1ab32c423531b90ce07db0482f8ad229b2d01db1` and registry request
`ebfb90d06` are accepted for focused validation.  The isolated source commit
is `e601015588ad26dd95c860686d5cf1e5ea3bb123`; it changes exactly
`Lean/FabiusFunction/FabiusDecayComparison.lean` from current-main preimage
blob `300b7a26b30888c21fbb9301ed939ebfdeecb273` to blob
`5a407fe366bead3fa2bb8f9d90cac14900fc46bf`, SHA-256
`50D055DFE92CCB49DB871DC7E0CA0DCCB1A26B8874DDEB4CD0CD413075D8DA9D`.
Main's intervening document publication changes no Lean path or dependency.

Independent hostile review accepts the five new positive-`beta` APIs, the
dyadic-rpow and small-argument transfer algebra, all signs and filters, and
the necessity of `0 < c` and `0 < beta`.  The four existing `beta = 1`
declaration headers remain textually identical compatibility wrappers.  The
imports are unchanged and acyclic, no exact or semantic collision is visible,
and the two direct importers are exactly
`FabiusQuotientExponentialMismatch` and `PaperKFoldThueMorse`.  This is static
source evidence only; no Lean/Lake process has yet validated the checkpoint.

Grant this branch EVO's sole Lean/Lake token.  After fetching and rereading
this board, preserve the exact source blob above and run from the repository
root exactly these three commands, as separate strictly sequential
invocations and in this order:

```text
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.FabiusDecayComparison
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.FabiusQuotientExponentialMismatch
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.PaperKFoldThueMorse
```

Stop after the first nonzero exit.  Do not run a fourth/root/facade target,
another Lean/Lake process, TeX/PDF, cache clean/reconstruction, or any
canonical-document operation.  Record exact validation tree/commit, source
blob, commands, scheduled-job counts, exits, and all diagnostics in only the
branch registry; push only the feature branch and release the EVO token at the
handoff.  This grant conveys no source-integration or main-write authority.

## Checkpoint 2026-08-26 02:33 PDT

```text
observed main before this directive: 4789f05b1a1abc34b5753c166a524be1f62078c3
coordinator branch: codex/fabius-coordinator-20260825
integration mode: exact immutable sources -> coordinator -> fast-forward main
main write owner: coordinator
codexbox Lean/Lake owner: unassigned
  (IDLE)
codexbox TeX/PDF owner: unassigned
  (IDLE)
EVO Lean/Lake owner: unassigned
  (IDLE)
EVO TeX/PDF owner: unassigned
  (IDLE after the accepted provenance repair below)
documentation owner: unassigned
  (all canonical documents are frozen)
next poll: at the next immutable source or registry claim
```

**Canonical Lambert cluster exposition accepted and released.**  Exact atomic
repair `0752e6b5860e253c2b7e85256a7df59a2ca2d91d` is integrated as
`985865c12`.  Its TeX diff changes only the two fields authorized by the prior
checkpoint: the title-page date is now 26 August 2026 and the repository
snapshot is the full validated commit
`948bf3f377472c068f9539e0569d383ddc35f617`.  The accepted theorem
exposition, formulas, 25 Lean mappings, bibliography, labels, and remaining
layout source are byte-preserved from candidate `1a92da844`.

The final TeX is blob `194881d2cd8c66144f35dd4dca7643656766e686`,
SHA-256
`F175FD094B55772E4F44F8196F749EB0434ECA32403AB4607260AA908FC887AD`,
200,759 bytes.  The matching PDF is blob
`3f3fac8fca3caa75bc44ece13db1df124022c6cf`, SHA-256
`A15710C45F647331D1EDE416F1BF4F1D8D597B5CDFAFC8A374C629F50AE1D820`,
1,025,979 bytes and 60 A4 pages.  The worker's three fresh sequential
`pdflatex` passes exited 0 and settled at 58/60/60 pages.  Independent
coordinator checks reproduced 380 unique labels with no duplicate or missing
reference, 22 unique bibliography items with no duplicate or missing cite,
449 balanced environments, 23/23 embedded and subsetted fonts, no PDF
suspects, and no rendered `??`.  Pagewise extracted-text comparison against
the accepted predecessor changes only page 1; a fresh 180-DPI inspection of
that page confirms the complete commit, date, alignment, and glyph rendering.
`git diff --check` is green.

Registry handoff `8b3e8033d` correctly retracts the premature earlier
all-audits-green sentence, records the harmless 63-hex digest typo in the old
candidate commit message, and releases the pair.  Only its exact final 98-line
handoff block is curated into the coordinator tree; the feature's long-lived
registry history is not imported wholesale.  No Lean/Lake or additional
TeX/PDF command ran during coordinator integration.  The canonical primary
pair, theorem-polish document lease, and EVO TeX/PDF stream are accepted and
released, and no successor document claim is active.

## Checkpoint 2026-08-26 02:21 PDT

```text
observed main before this directive: 447ea43628edf6d4f868aaac596574673412ef3d
coordinator branch: codex/fabius-coordinator-20260825
integration mode: exact immutable sources -> coordinator -> fast-forward main
main write owner: coordinator
codexbox Lean/Lake owner: unassigned
  (IDLE after the green inverse endpoint/facade sequence below)
codexbox TeX/PDF owner: unassigned
  (IDLE)
EVO Lean/Lake owner: unassigned
  (IDLE)
EVO TeX/PDF owner: codex/fabius-theorem-polish-20260825
  (ACTIVE: only the title-page provenance repair granted below)
documentation owner: codex/fabius-theorem-polish-20260825
  (SOLE OWNER of that exact canonical primary TeX/PDF repair)
next poll: at the repaired primary handoff or the next immutable source claim
```

The coordinator has accepted and validated the following independently
reviewed, path-isolated Lean units since main `1eadfd565`.  These mappings are
source-only integrations; no moving feature history or branch registry was
merged:

- formal Lambert fixed-point source `06ff742b7` -> `afa1d70a8`, with
  coefficient repair `b59008f69`; the transitive
  `+FabiusFunction.FabiusLambertAllOrderSmallArgument` gate exited 0 after
  3261 jobs;
- affine real Prouhet source `15c8fbf4f` -> `1813aaa3e`, with direct-real
  import repair `2228203af`; Prefix, UniformSpline, ComplexShiftSpline, and
  Computability gates exited 0 after 2022, 3415, 3417, and 3424 jobs;
- zero-odd-subsequence source `6818db074` -> `094030b56`; AnalyticMoments and
  FabiusLegendreSeries gates exited 0 after 2828 and 3252 jobs;
- XOR source `e91a2828c` -> `2a9c9fab1`, with induction-motive repair
  `b0c9a1e1c`; ThueMorseBinomialLog exited 0 after 2024 jobs;
- Lambert-tail relocation `b330296cf` -> `7c498984d`; TailFlat,
  SharpAsymptoticTransfer, and FullAsymptoticExpansion exited 0 after 3344,
  3344, and 3561 jobs;
- negative-Laplace kernel normalization `ab1d4c35d` -> `ce9e9c455`;
  NegativeLaplace and BoseFinitePartIntegral exited 0 after 2834 and 3271 jobs;
- Proposition 22 comment repair `64e756787` -> `6cc0f9091`; PaperStatements
  exited 0 after 3245 jobs;
- current-engine replay of simultaneous Wikipedia-error source `30a02d4a7`
  -> `6ed41b220`; FabiusWikipediaObstruction exited 0 after 3704 jobs;
- odd-count mod-three source `df9ed711e` -> `4c07ffd10`;
  ThueMorseBinomialLog exited 0 after 2024 jobs;
- iterated-divX functoriality source `fc52866e4` -> `93e04fcfb`;
  FabiusSaddleReferenceWeight exited 0 after 3520 jobs; and
- Gaussian-integrability consolidation `d0e2ea48d` -> `e050e654e`; Central,
  ReferenceTail, MassAllOrders, and FullAsymptoticExpansion exited 0 after
  3437, 3438, 3550, and 3561 jobs.

The only diagnostics in those successful gates were the already recorded
inherited `ProbabilityLaplaceMoments.lean` linter where its import closure was
replayed.  Every listed path and the codexbox token are released.

**Inverse elementary-scale hierarchy accepted.**  The exact endpoint/facade
blobs from synchronized tree `f2b62161a` were integrated as `447bd821a`.
The first target run exposed only proof-elaboration normalization defects;
statement-preserving repairs `4aadd3504`, `9b3bc8ff9`, and `4cde67c7a` make
method chaining explicit, unfold function-space applications, and normalize
the two affine/radical ring identities.  The final endpoint blob is
`b02fd05fae88d0521930281e09c0813daee97650` (SHA-256
`98C3C0DD76A1D1424357C31C05EA8DE9D9FAE350515DC0551997F6B05F37132F`);
the facade remains exact blob
`ce830f045e45e291a969f4d97a41294d8f83494a` (SHA-256
`1367FAF472A6667F02D8C3403CF417B853E0FDEC5B02740583F134211EF96F65`).

Lake 5.0 ignores `LAKE_JOBS` as a worker-pool limit.  After the EVO cold-cache
failure and one promptly interrupted codexbox probe exposed that fact, the
repository-prescribed `LEAN_NUM_THREADS=0` control was added; no cache clean or
reconstruction occurred.  With dependencies serialized and warm, the exact
commands

```text
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.FabiusInverseAsymptotic
LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction.PaperFabiusAsymptotic
```

ran separately in that order and exited 0 after 3934 and 3963 jobs.  Both
reported only the inherited `ProbabilityLaplaceMoments.lean` linter.  The two
hierarchy declarations, facade prose, all associated source paths, and both
Lean/Lake tokens are accepted and released.  Canonical inverse documentation
remains frozen; the future-doc scope in the preceding checkpoint remains
binding.

The primary Lambert-cluster candidate `1a92da844` and its exact 97-line
registry release block are preserved on the coordinator branch but are not
accepted into main.  The title-page snapshot mismatch found by hostile review
remains the sole blocker, and checkpoint `447ea4362` grants only its exact
repair/re-render.  Do not treat the candidate blobs or the old all-audits-green
registry sentence as settled evidence.  No other document owner exists.

## Checkpoint 2026-08-26 02:13 PDT

```text
observed main before this directive: a949e2efaa485283e66a7d2130fc723168c01efa
coordinator branch: codex/fabius-coordinator-20260825
integration mode: exact immutable sources -> coordinator -> fast-forward main
main write owner: coordinator
codexbox Lean/Lake owner: coordinator
  (IDLE after the failed inverse-hierarchy target gate; repair audit active)
codexbox TeX/PDF owner: unassigned
  (IDLE)
EVO Lean/Lake owner: unassigned
  (IDLE after infrastructure-only failure and explicit release)
EVO TeX/PDF owner: codex/fabius-theorem-polish-20260825
  (ACTIVE: exactly the narrow primary provenance repair below)
documentation owner: codex/fabius-theorem-polish-20260825
  (SOLE OWNER of the exact canonical primary TeX/PDF repair below)
next poll: at the repaired document handoff or inverse source-repair checkpoint
```

**Canonical Lambert cluster exposition provenance repair.**  Independent
review accepts the mathematics, all 25 Lean mappings, cluster interval,
liminf/limsup formulas, every-real-constant obstruction, static TeX checks,
and the rendered artifact in candidate `1a92da844`.  Integration is withheld
because the title page still identifies the old 25-August snapshot
`8d928a55f`, at which the 25 newly mapped declarations do not exist, while the
bibliography correctly identifies validated 26-August snapshot `948bf3f37`.
The PDF therefore contains incompatible source provenance.  The atomic
commit message also truncates the correct 64-hex PDF SHA-256 by its final `B`;
the actual artifact and registry digest ending `...BAC2B` are correct, so no
history rewrite is requested.

Grant `codex/fabius-theorem-polish-20260825` sole ownership of exactly:

- `docs/Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex`;
- its matching canonical `.pdf`; and
- `docs/registry/codex-fabius-theorem-polish-20260825.md`.

The only authorized TeX content repair is the title-page snapshot date
25 August -> 26 August and commit `8d928a55f...` -> `948bf3f37...`.
Do not alter the accepted quotient/cluster exposition, bibliography snapshot,
Lean mappings, labels, formulas, layout, or any other path.  First merge and
reread this checkpoint.  Then run exactly three strictly sequential
`pdflatex -interaction=nonstopmode -halt-on-error` passes in one fresh
external staging directory.  Accept only a settled third pass with no
undefined reference/citation, rerun, changed-label, fatal, emergency-stop, or
new/changed box diagnostic.  Repeat label/reference/citation/environment,
PDF metadata, embedded-font, extracted-text, rendered-`??`, and page-one
raster checks; inspect any other page whose text or pagination changes.  Push
only the feature branch, record exact final TeX/PDF blobs, SHA-256 values,
sizes/pages/log diagnostics, correct the earlier all-audits-green claim, note
the commit-message digest typo, and release the pair and EVO TeX/PDF stream.
No Lean/Lake, coverage, walkthrough, frontier, README, root, facade, or other
document path is granted.

**Inverse hierarchy validation failures and hold.**  EVO handoff `0a1757e529`
records that `LAKE_JOBS=1` did not constrain Lake 5.0's worker pool: the cold
3931-job run spawned concurrent Lean children and exited before the requested
target on transient missing `.olean.private` reads, the documented OOM/cache
race signature.  The worker correctly skipped the facade gate and released
the token.  A coordinator retry confirmed that `LEAN_NUM_THREADS=0` is the
effective worker-pool control and then reached the exact endpoint target, but
that target exposed genuine elaboration errors in the new hierarchy source.
No facade gate ran.  Source/API statements remain frozen while independent
proof-only repair review is active; no branch receives a retry or source-edit
grant from this checkpoint.  Do not clean or reconstruct any cache.  A later
explicit checkpoint will bind a statement-preserving repair and the exact
serialized retry commands with both `LEAN_NUM_THREADS=0` and `LAKE_JOBS=1`.

## Checkpoint 2026-08-26 01:51 PDT

```text
observed main before this directive: 1eadfd565db2e4c49310dbaa68c7b4648cb563b8
coordinator branch: codex/fabius-coordinator-20260825
integration mode: exact immutable sources -> coordinator -> fast-forward main
main write owner: coordinator
codexbox Lean/Lake owner: coordinator
  (ACTIVE: one serialized FabiusWikipediaObstruction gate)
codexbox TeX/PDF owner: unassigned
  (IDLE)
EVO Lean/Lake owner: codex/fabius-inverse-asymptotic-20260825
  (ACTIVE: exactly the two inverse-hierarchy targets below)
EVO TeX/PDF owner: unassigned
  (IDLE after the pushed Lambert cluster exposition handoff)
documentation owner: unassigned
  (IDLE; the candidate primary pair is frozen pending coordinator review)
next poll: at the inverse branch's validation handoff or the primary-pair audit
```

**Inverse elementary-scale hierarchy validation grant.**  The synchronized
source tree `f2b62161ac3d21fac027bc3acfc3e4f44ed18dd5` on
`codex/fabius-inverse-asymptotic-20260825` is accepted for validation; registry
tip `e41a08520b571e1b1591598a1065f205209a3146` records the retarget.  The final
source blobs are `fd3b5dac6c3f25332c130967ec4914343b7b506a` for
`FabiusInverseAsymptotic.lean` and
`ce830f045e45e291a969f4d97a41294d8f83494a` for
`PaperFabiusAsymptotic.lean`; the already-green generic engine remains
`8017000f51c7c57408963d76f436fb8d9a36137f`.

Independent mathematical, API/elaboration, topology, facade, and collision
audits accept exactly the two additive declarations
`rpow_isLittleO_fabiusInv_at_zero_right` (for every `alpha > 0`) and
`fabiusInv_isLittleO_negLog_rpow_at_zero_right` (for every real exponent),
including their one-sided filters, exponent-gap signs, real-power rewrites,
and equivalence-transfer directions.  The synchronized source preserves all
earlier compiler-driven endpoint/facade repairs and every existing public
header/import.

On EVO, run from the repository root, as two separate strictly sequential
invocations and in exactly this order:

```text
LAKE_JOBS=1 lake build +FabiusFunction.FabiusInverseAsymptotic
LAKE_JOBS=1 lake build +FabiusFunction.PaperFabiusAsymptotic
```

Run no generic-engine replay, root aggregate, third target, parallel
Lean/Lake process, or TeX/PDF command under this Lean grant.  Record the exact
source state, command, job count, exit code, and complete diagnostics for each
gate; stop after the first failure.  Push only the feature branch, update only
its own registry, and release the EVO Lean/Lake token explicitly at the
handoff.  The independent theorem-polish TeX/PDF stream may coexist under the
one-Lean-plus-one-TeX-per-host policy, but the two streams must not launch a
second process of their own kind.  This grant confers no main-write, document,
facade-edit, root, or canonical-TeX/PDF ownership on the inverse branch.

The earlier board prose that referred to
`quadraticAsymptoticInversion_with_affine` used a stale proposal name.  The
accepted public theorem is `quadratic_asymptotic_inversion`; this checkpoint
corrects the control-plane spelling only.  Canonical inverse documentation
remains frozen.  A future separately granted documentation tranche may map
only accepted phase, sharp-equivalent, and scale-hierarchy declarations and
must state that Lean proves the logarithmic comparison for every real
exponent.

Theorem-polish has completed the separately granted primary exposition and
pushed atomic TeX/PDF source commit `1a92da844` plus registry handoff/release
`63e66f6b5`.  Its document ownership and EVO TeX/PDF stream are released now;
no additional edit or render is authorized.  Candidate blobs
`b953cdd98010b882bfecb2b251861f65218c6329` (TeX) and
`d7fc37be89ce21dfab2630f62b682e273b4c6b99` (PDF) remain frozen and are not yet
an integration claim from this checkpoint.  The coordinator will accept or
reject only that atomic pair after independent formula, static, font, text,
raster, and ancestry review; do not merge the moving feature history.

## Checkpoint 2026-08-26 01:18 PDT

```text
observed main before this directive: 948bf3f377472c068f9539e0569d383ddc35f617
coordinator branch: codex/fabius-coordinator-20260825
integration mode: exact immutable sources -> coordinator -> fast-forward main
main write owner: coordinator
codexbox Lean/Lake owner: coordinator
  (IDLE after strict-moment and inverse-diagonal validation)
codexbox TeX/PDF owner: unassigned
  (IDLE)
EVO Lean/Lake owner: unassigned
  (IDLE)
EVO TeX/PDF owner: codex/fabius-theorem-polish-20260825
  (ACTIVE: one strictly sequential primary-document stream)
documentation owner: codex/fabius-theorem-polish-20260825
  (SOLE OWNER of the exact canonical primary TeX/PDF pair below)
next poll: at that branch's pushed source/render handoff or the next immutable
  Lean source handoff, whichever arrives first
```

Two reviewed additive Lean units were integrated selectively after the prior
checkpoint.  Effective-bounds source `b044a0ec9` is integrated as
`1cd536240`; it exposes all-real strict decrease of raw Fabius Laplace moments
and positivity of normalized moments while preserving the old nonnegative
headers as compatibility wrappers.  Serialized builds of
`+FabiusFunction.LaplaceMomentBounds` (3417 jobs) and
`+FabiusFunction.NegativeLaplaceDerivativeBounds` (3419 jobs) both exited 0,
with only the inherited `ProbabilityLaplaceMoments.lean` linter.  Both-papers
sources `7e4ec3657` and `8ee25ba02` are integrated in dependency order as
`d748b0bdf` and `ff9f6386d`; they classify the three forward and inverse
diagonal intersections.  Two initial focused attempts exposed only an
elaboration failure from applying the reducible `StrictConvexOn` conjunction
projection directly and supply no validation evidence.  Proof-only repair
`7235b61fe` destructures that conjunction before applying its strictness field,
without changing any declaration.  The retry of
`+FabiusFunction.FabiusInverse` completed 3248 jobs and exited 0 without
warnings.  These Lean paths and the codexbox token are released.

**Canonical Lambert cluster exposition grant.**  Registry checkpoint
`627931a0b` on `codex/fabius-theorem-polish-20260825` is approved.  Its clean
feature merge `1af1aa904` contains current main `948bf3f37` and preserves the
validated cluster-set Lean blobs.  The branch is the sole relaxed document
owner for exactly:

- `docs/Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex`;
- `docs/Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.pdf`;
  and
- `docs/registry/codex-fabius-theorem-polish-20260825.md`.

The canonical starting blobs are exactly TeX `5071d1f32f5f732e7cc59f569190532b6d815d57`
and PDF `4529d9c453d647e4068e2ff5527c417f5564f5d0` on both current main and the
feature.  No other document, source, facade, root, coverage, walkthrough,
frontier, README, audit, coordination, or peer-registry path is granted.  In
particular, do not import the stale shifted-prefix primary PDF or resolve a
binary PDF conflict; rebuild the owned PDF only from the owned current-main
TeX.

The bounded prose change may replace the obsolete multiplier-one warning with
the formalization-backed corrected quotient model, its complete cluster
interval
`[exp negativeLaplacePsiPeriodMin, exp negativeLaplacePsiPeriodMax]`, the exact
variational liminf/limsup formulas and strict gap, and failure of every real
constant normalization.  Map these claims to the exact validated declarations
in `FabiusWikipediaMain`, `FabiusWikipediaObstruction`, and
`FabiusSharpAsymptotic`.  Do not claim numerical extrema, a unique extremizing
phase, signs of the extrema, or a finite elementary closed form.

The branch also holds EVO's sole lightweight TeX/PDF stream for this unit.  It
may edit, commit, and push only the three owned paths and may run exactly three
strictly sequential
`pdflatex -interaction=nonstopmode -halt-on-error` passes for the primary
document.  Run no Lean/Lake process, no parallel TeX process, no `latexmk`, and
no other TeX compiler.  If TeX is repaired after a pass, restart and settle a
fresh three-pass sequence; never install a failed or mismatched PDF.

Before handoff, require `git diff --check`, unique labels and bibliography
keys, resolved references/citations, balanced environments, a final pass with
exit 0 and no undefined-reference/citation, rerun, changed-label, fatal,
LaTeX-error, or new/local overfull-box diagnostic.  Inspect and report any
underfull warning.  Verify page size/count, embedded fonts, extracted text
without rendered `??`, and rasterize/inspect every page changed directly or by
cross-reference/section renumbering.  Commit the TeX and its matching settled
PDF atomically, track no auxiliaries, record exact commands/exits/hashes/sizes/
pages/diagnostics, push only the feature branch, and release the pair and EVO
stream explicitly in its own registry handoff.  No further micro-grant is
needed for bounded sequential repair/rebuild iterations within these rules.

## Checkpoint 2026-08-26 00:58 PDT

```text
observed main before this directive: fc63c39788ab4c31694e4f57efe05b543165675a
coordinator branch: codex/fabius-coordinator-20260825
integration mode: exact immutable sources -> coordinator -> fast-forward main
main write owner: coordinator
codexbox Lean/Lake owner: coordinator
  (IDLE after the sharp inverse and exact cluster-set validations)
codexbox TeX/PDF owner: unassigned
  (IDLE)
EVO Lean/Lake owner: unassigned
  (IDLE; both pending requests were validated by the coordinator instead)
EVO TeX/PDF owner: unassigned
  (IDLE)
documentation owner: unassigned
  (IDLE; every canonical document path is frozen)
next poll: at the next immutable source or serialized-path claim handoff
```

Four reviewed source units have been integrated selectively since the prior
checkpoint; no moving feature history or worker registry was merged wholesale.

1. Effective-bounds source `51b9ad393` sharpens the all-real positive-index
   binary-reduction summand constant from four to three and removes the single
   redundant private regularity helper.  It is integrated as `942fd6b68`; the
   final `FabiusBinaryReductionSeries.lean` blob is `637e4bb0a`, SHA-256
   `92FCDB215915F68A2458A42885046B3A31A71CEC03BE34AC5B5A11C9BD0E0626`.
   Separate serialized builds of `+FabiusFunction.FabiusBinaryReductionSeries`
   (2820 jobs) and `+FabiusFunction.FabiusGlobalQBinomialSeries` (3324 jobs)
   both exited 0.  One preliminary command from a nested directory had no Lake
   configuration, exited before launching Lean, and supplies no evidence.
2. Both-papers source `a72ca3c92` deletes only three unused private lemmas from
   `LegendreSeriesConvergence.lean` and `OriginalUniqueness.lean`, ten lines in
   total and no public API.  It is integrated as `611fb96ff`; the result blobs
   are `2c02832f0` and `b29edf55a`.  Separate serialized builds of
   `+FabiusFunction.OriginalUniqueness` (3244 jobs) and
   `+FabiusFunction.LegendreSeriesConvergence` (2715 jobs) both exited 0.
3. Inverse-asymptotic source `9b7affe68` adds the generic quadratic inversion
   theorem, endpoint source `6ee65a167` adds the sharp left/right Fabius inverse
   formulas, and facade source `d6464f6c8` exposes the endpoint module through
   `PaperFabiusAsymptotic`.  They are integrated as `431425975`, `18e7c6dcf`,
   and `504ed4892`.  Initial focused compilation exposed only proof-normal-form,
   missing-topology-scope, and facade-subject wording defects; those attempts
   supply no validation evidence.  Statement-preserving repairs `863954b6a`
   and `6d5a6c09c` use explicit function/Pi normal forms, a robust
   difference-of-squares cancellation, the required topology scope, exact
   one-sided-set membership, and the accurate subject
   `Real.log (fabiusInv F hF y)`.  Final blobs are `8017000f5`
   (`QuadraticAsymptoticInversion.lean`), `756e7a50a`
   (`FabiusInverseAsymptotic.lean`), and `35a9c87fa`
   (`PaperFabiusAsymptotic.lean`).  Serialized builds completed
   `+FabiusFunction.QuadraticAsymptoticInversion` (2011 jobs),
   `+FabiusFunction.FabiusInverseAsymptotic` (3931 jobs), and
   `+FabiusFunction.PaperFabiusAsymptotic` (3960 jobs), all exit 0; the latter
   two replayed only the inherited `ProbabilityLaplaceMoments.lean` linter.
4. The theorem-polish cluster-set unit is the exact cumulative sequence
   `305d71e3f`, `46a8e3d8f`, and `ba7eebad0`, integrated in dependency order as
   `0e283d01f`, `9830baf09`, and `508341204`.  It exposes the literal compact
   Lambert factor, the exact periodic phase cluster engine, and the full
   quotient cluster interval/liminf/limsup/no-constant-repair API.  The first
   focused Sharp build compiled the two upstream modules and exposed only
   elaboration normal forms in the final module: an untyped constant defaulted
   to `Nat`, composed functions needed `Function.comp_def`, Pi addition needed
   `Pi.add_def`, and `IsLeast`/`IsGreatest` bound points were implicit.  Repair
   `e332a58fd` changes no statement, removes one new unused-simp warning, and
   produces final blobs `c8b9cb20e`, `f69e4d35a`, and `ad9ca03af`.  The retry
   of `+FabiusFunction.FabiusSharpAsymptotic` completed 3891 jobs and exited 0.
   Because the inverse endpoint imports this changed Sharp layer, fresh
   serialized downstream builds of `+FabiusFunction.FabiusInverseAsymptotic`
   (3931 jobs) and `+FabiusFunction.PaperFabiusAsymptotic` (3960 jobs) also
   exited 0.  All three reported at most the already accepted inherited
   `ProbabilityLaplaceMoments.lean` linter.

All source paths above, the codexbox token, and both requested EVO tokens are
released.  No source owner, build owner other than the idle coordinator, or
document owner remains.  In particular, the shifted-prefix reciprocity
documentation checkpoint is preserved but not integrated: its coverage and
walkthrough units are semantically sound, while its old primary TeX/PDF pair
predates and would erase the accepted compact-Lambert section.  The textual
primary hunks may be proposed later only under a fresh exact-path document
grant followed by a new matching PDF build.  Do not merge its moving branch or
install its old primary PDF.  All canonical documents remain frozen.

## Checkpoint 2026-08-25 23:30 PDT

```text
observed main before this directive: 741db6b4b777abc3fb4ca9ba6a6f0f098399c1bb
coordinator branch: codex/fabius-coordinator-20260825
integration mode: feature branches -> coordinator -> fast-forward main
main write owner: coordinator
codexbox Lean/Lake owner: coordinator
  (IDLE after general Kummer/carry-cocycle validation)
codexbox TeX/PDF owner: unassigned
  (IDLE)
EVO Lean/Lake owner: unassigned
  (IDLE; the coordinator supplied the accepted compact-Lambert gate)
EVO TeX/PDF owner: unassigned
  (IDLE after the settled primary-exposition handoff)
documentation owner: unassigned
  (IDLE; all canonical documents frozen)
next poll: at the next immutable source or serialized-path claim handoff
```

The previously approved curvature, generalizations, lower-Lambert,
exposition, and theorem-polish tranches remain on `main`.  One merge tip
incorporating two paused feature histories advanced `main` from `f74396e5a` to
`1570b29b9`: 28 commits became newly reachable and produced an 18-path net
delta.  Three independent audits are complete.  The exact translated-polynomial
source, all nine non-semantic Lean/root/facade deltas, the isolated
non-elementarity TeX/PDF pair, the audit fence repair, and the two Claude
registry updates are accepted.  The exposition and theorem-refinements
registries are retained with snapshot corrections, and the sole coverage-link
defect is fixed forward.  The first exact root build then caught one parse-only
defect: a new `partialSum_smul` doc comment sat between `@[simp]` and `theorem`.
The syntax-fix commit moves the comment before the attribute.  The retry at
immutable `9887ea584` passed the complete `+FabiusFunction` aggregate (4008
jobs, exit 0).  The integration incident is closed; no revert or duplicate
cherry-pick is needed.

Main commit `c5ee98fc7` adds four user-supplied TeX inputs under
`docs/non-formalized-research-frontiers/drafts/` and changes no existing
canonical document, Lean file, registry, or control file.  Preserve those
7,247 lines as an unreviewed temporary frontier inbox under the existing
draft-disposition rules.  They confer no document ownership and must not be
compiled, integrated, deleted, or moved while documentation is frozen.

## Immediate shared instructions

1. **Feature-branch work is open.**  Any worker may make local changes, commit
   frequently, and push its own named feature branch.  Before editing ordinary
   paths, push a `SYNC Fabius` claim in that branch's registry naming the exact
   paths and expected declarations or document claims; fetch/read this board
   and inspect advertised registries/tips for overlap and plausible duplicate
   declarations.  If the claim is nonoverlapping and avoids the serialized
   paths below, work may begin without coordinator acknowledgement.  Push
   feature branches only; the coordinator is the sole `main` writer.  Never
   force.
2. Lean/Lake/cache-mutating compilation remains serialized to one assigned
   process per physical host.  Workers without a host Lean/Lake grant may edit
   and commit unvalidated work, but launch no such process; label those commits
   and registry reports `Not yet validated`.  A board-assigned document owner
   may run one sequential LaTeX/PDF tool stream on its assigned host without
   consuming that host's Lean token, and that stream may coexist with the one
   assigned Lean build.  No document worker or TeX stream is currently
   assigned.  Do not launch a TeX pass or terminate another process without a
   later board grant.
3. The following remain serialized and require an explicit board grant:
   `AGENTS.md`, `README.md`, `docs/COLLABORATION.md`,
   `docs/MULTI_AGENT_COORDINATION_PROPOSAL.md`, `docs/PAPER_COVERAGE.md`,
   `docs/AUDIT_FINDINGS.md`, this board, the root aggregate
   `Lean/FabiusFunction.lean`, and every primary-exposition, walkthrough, or
   canonical-frontier TeX/PDF path.  Any path marked hot, frozen, or
   single-owner below is also unavailable to ordinary claims.  The former sole
   document exception has now been settled and released; coverage, primary,
   walkthrough, frontier, every draft, and every other canonical document are
   frozen.  Host Lean/Lake ownership is tracked separately from the
   lightweight document lane.
4. Preserve dirty work before merging.  Never stash, reset, discard, or
   overwrite it.  A checkpoint/WIP commit is acceptable on a feature branch if
   its message states exactly what remains uncompiled or unfinished.  After a
   clean/checkpointed push and a fresh board read, workers may merge
   `origin/main` into their own feature branches.  Resolve only conflicts
   wholly within an uncontested claim; report and stop on serialized, generated,
   or multiply claimed paths.
5. Before proposing a theorem, search current `main`, all advertised Fabius
   branch tips, and registry files for the declaration and plausible alternate
   names.  Report a pivot rather than adding a duplicate.
6. A claim expansion follows the same protocol: advertise and push the added
   exact paths before editing them.  If two advertised claims overlap, neither
   worker edits the overlap until one pivots or this board assigns ownership;
   nonoverlapping portions may continue.
7. Push preservation checkpoints promptly.  The coordinator may prune a
   worktree after seven days without activity, even when it is dirty.  Pushed
   commits and remote branches survive pruning; uncommitted changes do not.

## Active path map and branch-specific instructions

### `codex/fabius-generalizations`

All five source commits and the registry are integrated through `9a12a8736`;
the thirteen-path lease is released and the prior task is complete.  This
branch may begin new ordinary, nonoverlapping work under the shared protocol;
the released paths are not implicitly re-leased.
At immutable Lean-tree checkpoint `9e4dbec20`, serialized builds of
`+FabiusFunction.BromwichSaddle` and
`+FabiusFunction.PaperFabiusAsymptotic` both exited 0.  The same source tranche
is also covered by the later green combined paper-facade build at `60458909a`.
Two review notes remain for a future assigned cleanup: the public one-order
Lambert-tail bound is a lower-dependency specialization of the all-order
theorem, and the new half-endpoint range theorem subsumes a downstream
upper-bound lemma whose name should survive as a wrapper.

### `codex/fabius-lean-walkthrough-merge`

Registry checkpoint `db4ef7a31` is accepted as the sole advertised successor
request for the canonical frontier.  The live branch tree itself is not an
acceptable integration base: it is 195 main commits behind the reviewed
checkpoint, contains the obsolete six-part/172-page document pair, and a
read-only merge conflicts in exactly the frontier README, TeX, and PDF.  Do not
merge that stale tree, select either PDF side, or resolve those conflicts.

The workstream must preserve its pushed historical branch, then create a fresh
continuation branch named `codex/fabius-frontier-successor-20260825` from the
coordinator checkpoint carrying this directive.  The pinned input blobs are:

- frontier README `be3865b4b7fabbf09f3af9ce96f7e72098c0cb08`;
- frontier TeX `b284a5e4b7eaef66cf8c38637484b7ac109e945a`;
- inherited, mismatched and frozen PDF
  `0cd676c1d8d1f590acadd813ad42669c8faa5aba`.

**Source-phase grant.**  On that fresh base, this successor owns only the
frontier TeX and its existing branch registry for one checkpoint.  Apply
exactly the three advertised prose hunks around TeX lines 7317--7333: qualify
the blanket direct-corollary introduction, mark `dyadicweb:eq:D-error` as
frontier-dependent on the unformalized shifted-spline estimate, and qualify the
closing blanket paragraph.  Change no formula, theorem, label or reference
*target*, citation, environment, layout token, README, PDF, Lean file, primary
document, or other path.  The single literal
`\eqref{dyadicweb:eq:shifted-spline-bound-local}` in the advertised middle
hunk is explicitly authorized and is expected to increase the reference-token
count by one; it is not a contract violation.  Correct the registry's stale
fetched-main/HEAD fields and state
explicitly that this is a separate successor task with no primary scope.
Commit and push the TeX plus own-registry source checkpoint, then stop for an
independent source audit.

No TeX/PDF/build token is granted.  The canonical PDF remains frozen.  Only
after that exact source checkpoint passes review may the board separately
grant one host token for exactly three sequential `pdflatex` passes and the
post-render inspection.  The eventual render must rebuild the PDF; it must
never reuse or conflict-resolve the old binary.

Historical inputs remain preserved on the old branch:

- `docs/non-formalized-research-frontiers/README.md`
- `docs/non-formalized-research-frontiers/non-formalized-research-frontiers.tex`
- `docs/non-formalized-research-frontiers/non-formalized-research-frontiers.pdf`

The preserved 172-page rewrite source is `8142ccb19`; its registry handoff is
`8a53bd10a`.  Those bytes are evidence only, not the successor source base.

The successor complied on fresh base `f556a126e`: source commit `7bbd84752`
changes exactly the three advertised TeX prose hunks plus its new own registry,
and registry tip `ff6787ecf` freezes the source while reporting the now-resolved
single-`\eqref` ambiguity.  Its TeX blob is `6812dbf9caeab2c02fe92288f0524fa52256325b`
with SHA-256 `0AE36755EA52945E5032EF9005EA89CB59AAFA91EB36A1AC770FF2F0B53C63AB`.
Independent review passes: the exact paths/base/blobs and three prose hunks are
correct; all 986 labels are unique, every expanded reference and citation
resolves, all 1201 environments are balanced, and `git diff --check` is green.
The single added `\eqref` is the intended resolved dependency pointer.

**Three-pass PDF grant.**  This branch now holds the sole codexbox document
token.  First merge this coordinator checkpoint into the clean pushed feature
branch and verify that the TeX blob remains exactly `6812dbf9c`.  In
`Analysis/FabiusFunction/docs/non-formalized-research-frontiers`, run exactly
three sequential invocations of:

```text
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
  -jobname=non-formalized-research-frontiers_successor_7bbd84752 \
  non-formalized-research-frontiers.tex
```

Run no fourth pass, other TeX compiler, `latexmk`, Lean, or Lake, and make no
source edit during this grant.  The third pass must have: all three exits 0;
settled references/citations; zero undefined, rerun, changed-label,
multiply-defined, fatal, or LaTeX-error diagnostics; and zero overfull
horizontal or vertical boxes.  Then use only read-only `pdfinfo`, `pdffonts`,
`pdftotext`, and `pdftoppm` inspection.  Require embedded fonts, no rendered
`??`, and inspect the changed corollary paragraph, the page-184 table/footer,
and the page-10 opener.

If every gate passes, replace the canonical frontier PDF with the exact settled
third-pass output and commit/push only that PDF plus the successor registry;
the already-frozen TeX commit remains unchanged.  If any gate fails, do not
install a PDF or improvise a fourth pass/source repair: preserve the sidecar,
report exact diagnostics in the registry, push, and stop.  Never push `main`.

**Standing single-owner amendment.**  At the user's request, the preceding
per-hunk and exactly-three-pass restrictions are historical gates for
checkpoint `7bbd84752`/`daa9cb19f`, not the future operating model.  This is
now the only active documentation agent and holds a standing lease for exactly:

- `docs/non-formalized-research-frontiers/README.md`;
- `docs/non-formalized-research-frontiers/non-formalized-research-frontiers.tex`;
- `docs/non-formalized-research-frontiers/non-formalized-research-frontiers.pdf`;
- `docs/registry/codex-fabius-frontier-successor-20260825.md`.

Within those four paths it may choose and sequence bounded semantic-status,
human-readable-counterpart, organization, cross-reference, and layout work;
edit locally; commit and push feature checkpoints; and run the sequential
`pdflatex` passes plus read-only PDF/text/font/raster inspections needed to
settle a matching artifact, without requesting a new board acknowledgment for
each hunk or pass.  Advertise each bounded tranche in the own registry before
editing so source agents can see what is happening, but coordinator silence is
not a blocker.  It may update the frontier README and install a source-matched
canonical PDF when its own documented source/static/render gates pass.

This standing lease does not extend to a primary exposition, walkthrough,
campaign-wide Markdown/control-plane file, Lean source, or `main`.  It may not
run Lean/Lake, overlap multiple TeX/PDF processes, use force, or push `main`.
Its single sequential TeX/PDF stream may coexist with the one board-assigned
codexbox Lean/Lake build; neither lane may multiply itself.  On a failed
render, it may diagnose and repair its owned source and rerun as needed rather
than awaiting a micro-grant, but it must preserve/report rejected artifacts and
never install a mismatched PDF.  Release the standing lease explicitly in the
own registry when the frontier workstream is complete or paused.

The current human-readable backlog includes the eight newly validated
discrete-limit declarations, the complete complex Fourier zero locus, the
rational half-q root locus, and the uncorrected-Wikipedia non-equivalence
theorem.  The owner may disposition these in coherent frontier tranches under
the standing lease; it need not fold them into the already-built three-hunk
checkpoint.

The three-hunk checkpoint is now fully accepted and integrated by coordinator
merge `192c423bb`.  Source lineage `7bbd84752` and artifact commit `daa9cb19f`
produce TeX blob `6812dbf9c` and matching PDF blob `d2dd17022`, SHA-256
`225F8E17F9F8512DFCFBD9491AD5D2CA612537B66F1571DFA6F115FA76D904B8`.
The canonical artifact is 1,479,271 bytes, A4, and 188 pages.  Three independent
audits accept the ancestry/path scope, three-pass registry evidence, all 45
embedded/subsetted fonts, zero rendered `??` or out-of-bounds text, and clean
raster inspection of pages 1, 10, 83, 86, 95, and 184--188.  The accepted
source/PDF pair is now the base for the standing frontier lease; the owner may
continue future tranches without relinquishing that lease.

**Standing-lease release.**  The user reports that no documentation agents
remain active.  The successor branch's standing frontier lease and codexbox
TeX/PDF lane are therefore released; the accepted source/PDF pair above
remains the canonical frozen base, but the branch no longer owns or may edit
those paths merely by virtue of its historical work.  A future documentation
worker must first advertise an exact-path claim and receive a new board
assignment.  Once assigned, the relaxed single-owner operating model above
may be reused: no per-hunk micro-grants are required, and its one sequential
LaTeX stream may coexist with one host Lean build.

### `codex/fabius-both-papers`

The curvature workstream is fully integrated at `09ae23f63`; all old leases are
released and the prior task is complete.  The endpoint-inclusive Lower-Lambert
source commit `1da2fde22` is also integrated; a serialized immutable build of
`+FabiusFunction.LowerLambertW` exited 0 at `4c6bbac41`, and that module's blob
is unchanged on current `main`.  All Lower-Lambert, inverse-power, and
Gamma--zeta leases are released.  This branch may begin new ordinary work after
advertising exact files and declarations in its registry; it must still wait
for a board token before any validation process.

The natural-knot tranche is integrated through coordinator reconciliation
`068fc1be5`.  It adds exactly `extendedFabius_natCast_eq_ite` and
`iteratedDeriv_extendedFabius_natCast_eq_zero_iff` in
`Lean/FabiusFunction/GlobalExtension.lean`; existing signatures and downstream
special cases remain unchanged.  Independent proof/API review found no
implemented Lean duplicate and no theorem blocker.  The coordinator repaired
three elaboration sites at `62f4142a9`, then reconciled the worker's odd-witness
correction and registry at `068fc1be5`.

At immutable Lean tree `068fc1be5`, serialized one-job builds of
`+FabiusFunction.GlobalExtension` (2765 jobs) and
`+FabiusFunction.Paper06487` (3244 jobs) both exited 0.  The latter transitively
covers `PaperStatements` and `Paper06487Supplement`; `git diff --check` and the
forbidden-declaration scan are clean.  The `GlobalExtension.lean` lease is
released.  The branch may begin another ordinary nonoverlapping claim, but
must still receive a host token before running any validation process.

Exact feature tip `c41a52283` published four additional source units:

- dyadic-cast relocation `09b360531` across
  `Lean/FabiusFunction/GlobalDyadic.lean` and
  `Lean/FabiusFunction/OriginalPaperSupplement.lean`;
- strict Gamma--zeta sign API `ec23d663f` / `991add419` in
  `Lean/FabiusFunction/BoseFinitePartIntegral.lean`;
- inverse-power cast bridge `9458b1949` in
  `Lean/FabiusFunction/DyadicAnalytic.lean`;
- periodic dyadic-exponential helper consolidation `c7c2321bc` across
  `Lean/FabiusFunction/PeriodicRegularity.lean` and
  `Lean/FabiusFunction/PeriodicSmooth.lean`.

`GlobalExtension.lean` also has a doc-comment-only terminology edit.  Three
independent static reviews found no theorem, API, placement, duplicate,
dependency, import, or scope blocker.  The coordinator merged exactly
`c41a52283`, rather than the moving branch tip, at immutable integration merge
`04d619814`.  All eight focused targets and both minimal paper facades then
passed serially with `LAKE_JOBS=1`:

- `+FabiusFunction.DyadicAnalytic` (2772 jobs);
- `+FabiusFunction.GlobalExtension` (2765 jobs);
- `+FabiusFunction.GlobalDyadic` (2785 jobs);
- `+FabiusFunction.OriginalPaperSupplement` (3210 jobs);
- `+FabiusFunction.BoseFinitePartIntegral` (3268 jobs);
- `+FabiusFunction.PeriodicMean` (3269 jobs);
- `+FabiusFunction.PeriodicRegularity` (3295 jobs);
- `+FabiusFunction.PeriodicSmooth` (3297 jobs);
- `+FabiusFunction.Paper05442` (3417 jobs); and
- `+FabiusFunction.PaperFabiusAsymptotic` (3957 jobs).

Every invocation exited 0.  The seven source-path leases are released, and the
three corresponding proposal-era entries in `AUDIT_FINDINGS.md` are closed in
place.

Four later, mutually disjoint source units are now independently reviewed,
integrated by exact commit, and compiled without merging the moving feature
history:

- `d2df7eaa7`, private support-localization consolidation in
  `AnalyticMoments.lean`, integrated as `f975de00f`;
- `64a95d363`, the complete complex zero loci for `complexSinc`, the Fourier
  product, and the Rvachev transform in `FourierProduct.lean`, integrated as
  `f62058b96`;
- `a987b3bb9`, the rational finite-q-Pochhammer and half-q polynomial root
  loci in `HalfQBinomial.lean`, integrated as `29729991e`; and
- `45b4816c0`, the theorem that exponentiating the literal uncorrected
  Wikipedia logarithmic expression is not asymptotically equivalent to a
  bounded Fabius solution, integrated as `6f98e4804`.

All four exact parent blobs matched the current-main preimages.  Independent
proof/API reviews found no theorem, filter, sign, domain, import, duplicate,
attribute, consumer, or public-signature blocker.  The serialized builds listed
below all exit 0.  These four source paths are released.  Their human-readable
counterparts join the later frontier-document backlog and must not expand the
currently granted three-hunk source checkpoint.

Registry tip `9cbbbda1a` now advertises an ordinary one-file follow-up in
`PeriodicSmooth.lean`: `[simp]` bridges
`forwardDerivativeQuotientPolynomial_one`, `_two`, and `_three`, plus
`negativeLaplaceForwardTermDeriv_two`, `_three`, and `_four`.  No source is
committed at that registry snapshot.  Source commit `c5f0bb3a3` subsequently
implements exactly those six declarations.  Independent review accepts the
recurrence algebra, signs, derivative-index mapping, unconditional domains,
simp directions, placement, imports, and duplicate scan; main had the exact
parent preimage.

The coordinator integrated the exact source as `af3132a31`.  Its first focused
build exposed two proof-elaboration defects: polynomial normalization did not
close the second quotient identity, and a dependent rewrite failed at index
three.  It supplies no validation evidence.  Repair `8d269396a` proves the
three small polynomial identities by extensional evaluation and cleans the
bridge tactics, changing no public statement or attribute.  The retry of
`+FabiusFunction.PeriodicSmooth` completes 3297 jobs, exit 0, with no warnings.
The `PeriodicSmooth.lean` lease is released.

The branch next froze exact source commit `b27fc5259`, extending the
Reshetnikov oddness result to every natural index.  Two independent reviews
accept the zero and positive cases, the deliberate non-extension of the
valuation conjunct at zero, imports, API, and compatibility proof of
`theorem_nine_all`.  The coordinator integrated it as `6d15d9116`; serialized
builds of `+FabiusFunction.Paper06487Supplement` (3243 jobs) and
`+FabiusFunction.Paper06487` (3244 jobs) both exit 0.  The path is released and
the corresponding `AUDIT_FINDINGS.md` entry is closed.

Private-only source commit `6f8c8c046` then deletes the dead 22-line
`integral_unitInterval_max_sub_mul_pow` helper from `FabiusUniformSpline.lean`.
Two independent audits verify zero callers, identical public declaration
lists, and continued use of every retained import/helper.  The coordinator
integrated it as `b16fc9a6d`; `+FabiusFunction.FabiusUniformSpline` completes
3415 jobs, exit 0.  That path is released and its audit finding is closed.

Registry claim `1686a1a06` advertised an ordinary two-source tranche in
`Differential.lean` and `Existence.lean`: public generic bridge
`rvachevUp_hasDerivAt_of_fabiusReal_hasDerivAt`, specialization of the
unchanged `rvachev_hasDerivAt`, and replacement of the duplicate candidate
three-case proof while preserving `rvachevCandidate_hasDerivAt` and
`rvachevCandidate_even` exactly.  Independent preflight finds the hypotheses
sufficient in the negative, zero, and positive cases, the candidate use
noncircular, both current-main preimages unchanged, and no competing claim or
implementation.  Exact source commit `dbb7ace60` was integrated as
`12fda28c7`.  The first `+FabiusFunction.Differential` attempt exposed only a
generic-tail simplification mismatch at `rvachevUp F 1` and supplies no
validation evidence.  Statement-preserving repair `15563b7dd` makes the two
fold-endpoint zeros explicit.  At the repaired tree, separate serialized
builds of `+FabiusFunction.Differential` (2653 jobs) and
`+FabiusFunction.Existence` (2783 jobs) both exited 0 without warnings.  No
import, old public header, document, audit ledger, facade, or root path changed.
The two source leases and codexbox token are released.

Exact source commit `1b0792b2b5773879b94c07742b4e181c6afbe0d8`
adds only
`norm_normalizedThueMorseSplineBranch_add_sub_le_half_pow_mul_exp_all` in
`FabiusDiscreteLimitComplexShift.lean`.  Three independent audits verify the
vacuous empty-sum degree-zero case, truncated exponent, positive-degree
delegation, unchanged old APIs/imports/callers, exact current-main preimage,
and absence of a competing implementation.  The coordinator integrated it as
`f6cb1efd8`.  Separate serialized builds of
`+FabiusFunction.FabiusDiscreteLimitComplexShift` (1873 jobs) and its direct
consumer `+FabiusFunction.FabiusComplexShiftSpline` (3417 jobs) both exited 0
without warnings.  This implements only the first part of the broader audit
proposal; the audit entry remains open.  The source lease and codexbox token
are released.

The branch registry incorrectly spells that source SHA as nonexistent
`1b0792b2b22ed51b28404cc42175befb45313668` in three places.  Correct it in the
next own-registry checkpoint to the full SHA above; this bookkeeping defect
does not affect the integrated source or compiler evidence.

Registry claim `86c3c746b` advertises the disjoint downstream continuation in
`FabiusComplexShiftSpline.lean`: two all-degree/all-real translation bounds and
three all-real real/rational/Gaussian-rational convergence wrappers, with all
existing restricted APIs preserved.  The ordinary source-only claim is
nonoverlapping and may proceed in that one Lean file plus the own registry,
without Lean/Lake.  Keep the stronger `exp ‖δ‖ - 1` estimate open and touch no
audit ledger, document, facade, root, or other path.  An immutable source
checkpoint still requires exact review before any validation token.

Exact source commit `3c2d1e926` implements that continuation and was integrated
as `19ee18206`.  Two independent reviews accept all five declarations, including
the degree-zero, zero-coordinate, and nonpositive-real cases; exact source
blobs, imports, attributes, existing public headers, and the upstream all-degree
dependency were checked.  The old restricted theorem bodies remain
byte-preserved rather than being rewritten as literal wrappers, which is a
nonblocking compatibility choice.  A serialized
`+FabiusFunction.FabiusComplexShiftSpline` build completed 3417 jobs and exited
0 without warnings at the integrated tree.  This downstream continuation is
accepted, and its source lease and codexbox token are released.  The stronger
`exp ‖δ‖ - 1` frontier estimate remains open.

Exact source commit `3475f5ff0` is a later proof-only consolidation in
`ExactInversePower.lean` and `PaperStatements.lean`.  It replaces nine inline
`Finset.prod_pos` arguments with the canonical public
`oddDoubleFactorial_pos`, `evenMersenneProduct_pos`, and
`oddMersenneProduct_pos` lemmas, deleting 31 net lines.  Exact review verifies
that each replacement has the identical natural-number proposition and that
no declaration, header, attribute, import, caller, or docstring changes.  The
coordinator integrated it as `77e2f55d4`; serialized builds of
`+FabiusFunction.ExactInversePower` (2013 jobs) and
`+FabiusFunction.PaperStatements` (3242 jobs) both exited 0 without warnings.
Both paths and the codexbox token are released.

Registry-first claim `c31f3d733` advertises a disjoint ordinary one-file
tranche in `FabiusBinaryReductionSeries.lean`.  The six proposed names are
`norm_binaryReductionRemainder_le_total`,
`norm_globalBinaryReductionSum_sub_extendedFabius_le_total`,
`globalBinaryReductionSummand_eq_remainder_sub_all`,
`norm_globalBinaryReductionSummand_le_of_one_le_all`,
`summable_norm_globalBinaryReductionSummand_all`, and
`summable_globalBinaryReductionSummand_all`.  Exact preflight accepts the
scale-zero and all-real bounds, geometric summability, dependencies, API, and
duplicate scan.  Two conditions are binding: the summand/remainder identity
must retain `1 ≤ m`, because it is false at `m = 0`; and the inactive
serialized proposal to add a `Regularity` import and deduplicate a private
helper is excluded.  The final source report must also replace stale
complex-shift request fields in the branch registry.  Tip `c31f3d733` is
registry-only: ordinary source work may proceed in this file plus the own
registry, with every existing restricted header/attribute preserved, but no
build token is granted.  After an immutable reviewed handoff, the intended
gates are `+FabiusFunction.FabiusBinaryReductionSeries` and then its smallest
direct consumer `+FabiusFunction.FabiusGlobalQBinomialSeries`.

Exact source commit `13173290a` implements all six declarations and was
integrated as `9f4b6be52`.  Three independent reviews accept the scale-zero
residual, all-real telescope, essential `1 ≤ m` identity, `m = 1` majorant,
shifted geometric comparison, API, imports, and exact current-main preimage.
Every restricted declaration remains unchanged; only the body of the existing
uniform-convergence theorem is shortened through the new total estimate.
Registry checkpoint `beaff04ba` records the frozen source handoff and replaces
the stale request fields.  Separate serialized builds of
`+FabiusFunction.FabiusBinaryReductionSeries` (2819 jobs) and
`+FabiusFunction.FabiusGlobalQBinomialSeries` (3323 jobs) both exited 0 without
warnings.  The source lease and codexbox token are released; the excluded
`Regularity`/private-helper cleanup remains outside this tranche.

Registry-only claim `29e465362` advertised a new ordinary one-file tranche in
`PoissonSummation.lean`.  It proposes
`rvachevFourier_real_iteratedDeriv_shiftedDecay` for each `(k n : ℕ)`, with a
strictly positive constant bounding the `n`th real derivative by
`C * ((1 + |x|) ^ k)⁻¹`, and the order-zero wrapper
`rvachevFourier_real_shiftedDecay`.  Exact preflight accepts the Schwartz
seminorm argument, shifted normalization, zero-order and zero-weight cases,
placement, imports, and duplicate scan.  The constant may depend on
`F`, `hF`, `k`, and `n`; no uniformity in derivative order or on the complex
plane may be claimed.  Exact source commit `fe7756703` implements the two
declarations and factors the existing homogeneous proof through a private
Schwartz realization while preserving every old public header and import.
Two independent exact reviews accept the finite-seminorm constant, derivative
bridge, reciprocal inequality, all zero-order/zero-weight cases, exact
preimage, API, and collision scan.  The coordinator integrated only that
source as `49ddce559`.  Separate serialized builds of
`+FabiusFunction.PoissonSummation` (3195 jobs) and its sole direct public facade
`+FabiusFunction.Paper05442` (3417 jobs) both exited 0 without warnings.  The
source path and codexbox token are released.  No document, facade, root, import,
or other path changed; the branch's historical feature lineage was not merged.

Claim `84c22af63` then advertised deduplication of the continuous-coefficient
saddle polynomial across `FabiusSaddleExpansionCoefficients.lean` and its
direct importer `FabiusSaddleReferenceWeight.lean`.  Exact source
`036cbe4a2` deletes the 34-line primed private copy and mechanically rewires all
22 surviving downstream references.  Its initial registry language proposed
three public names; final handoff `9a5cf19e6` explicitly narrows the public API
to documented `negativeLaplaceExponentPolynomialContinuous` and
`negativeLaplaceExponentPolynomialContinuous_map`, retaining
`negativeLaplaceBoundedExponentJetContinuousMap` as a private constructor.
Independent audits accept that smaller abstraction boundary: the normalized
blocks are byte-identical, imports and every old public header/attribute are
unchanged, no primed reference remains, and there is no competing declaration.
The coordinator integrated only the exact source as `9aca1aaf3`.  Separate
serialized builds of `+FabiusFunction.FabiusSaddleExpansionCoefficients`
(3306 jobs) and `+FabiusFunction.FabiusSaddleReferenceWeight` (3517 jobs) both
exited 0; the latter replayed only the known nonblocking
`ProbabilityLaplaceMoments.lean` linter.  The source paths and codexbox token
are released.  This accepts the core deduplication but does not claim that the
audit proposal's optional three-name public surface was implemented verbatim;
the audit ledger itself remains unchanged and frozen.

Exact source `e8aa10cda` is the later one-file central-binomial valuation
tranche in `TwoAdic.lean`.  It adds
`centralChoose_padicValNat_two` and `thueMorseSign_centralChoose`, specializing
Kummer's digit-sum identity at two and then rewriting the defining
Thue--Morse sign.  Two independent actual-diff reviews accept the natural
subtraction, binary-digit shift, `n = 0` case, sign orientation, exact current
preimage, imports, API, and collision scan.  The coordinator integrated only
that source as `430aaac90`.  Separate serialized builds of
`+FabiusFunction.TwoAdic` (2017 jobs) and
`+FabiusFunction.Paper06487` (3244 jobs) both exited 0 without warnings.  The
source path and codexbox token are released; no document path is granted.
Worker handoff `eb90a1f7a` initially called `a585d729f` the source blob, but
that is the preimage; later own-registry handoff `8d765ffbd` correctly records
the accepted result blob `7295874def860ce52feb88655cae2338aa648078`.

Registry claim `e5ec81bd1`, exact source `48024a1d4`, and handoff
`8342c3af5` form the subsequent general Kummer carry-cocycle tranche in the
same `TwoAdic.lean` path.  It adds `addChoose_padicValNat_two` and
`thueMorseSign_add_valuation`, with one private subtraction-free digit-weight
balance helper.  Three independent reviews accept the all-natural Kummer
specialization, natural-subtraction elimination, sign orientation, zero and
carry-chain cases, API placement, exact preimage, and collision scan.  The
coordinator integrated only that immutable source as `598ad5850`.  Separate
serialized builds of `+FabiusFunction.TwoAdic` (2017 jobs) and
`+FabiusFunction.Paper06487` (3244 jobs) both exited 0 without warnings.  The
source path and codexbox token are released; no document, facade, root, or
other path is granted.

Claims `201f05612` and `8bf570c79` then advertised the exact three-path
negative-Laplace denominator consolidation.  Source `b369925e8` promotes the
existing private `exp_neg_div_one_sub_pow_le`, deletes the downstream local
copy, and redirects the two higher-derivative plus one periodic-second-order
callers.  Handoff `8d765ffbd` and clean sync `4ab7d97ad` preserve exact result
blobs `e5ddbd82d`, `10fcaaa74`, and `b343d7221`.  Independent review accepts
the all-natural-power estimate including `m = 0`, all three specializations,
the retained denominator-positivity fact, import topology, exact preimages,
eight consolidated calls, API preservation, and collision scan.  The
coordinator integrated only the isolated source as `a7946a7a9`.  Separate
serialized builds of `+FabiusFunction.NegativeLaplaceDerivativeBounds` (3419
jobs) and `+FabiusFunction.FabiusLambertDerivativeBounds` (3501 jobs) both
exited 0; the latter transitively rebuilt the edited
`LaplacePeriodicSecondOrder`.  Both reported only the inherited nonblocking
`ProbabilityLaplaceMoments.lean` linter.  The first gate's unrelated existing
`StepMeasureBridge` import took 728 seconds while broad abandoned search
processes caused temporary disk contention; serialization remained intact and
the build completed normally.  All three paths and the codexbox token are
released; no document, audit-ledger, facade, root, or other path is granted.

Exact private-cleanup source `a72ca3c92` subsequently deletes only
`legendre_weight_at_neg_one`, `legendre_weight_at_one`, and
`schwartzMap_apply` from `LegendreSeriesConvergence.lean` and
`OriginalUniqueness.lean`.  Each name had no caller; the endpoint values are
already proved directly and the surviving private Schwartz-map conversions
are definitional.  The coordinator integrated the isolated source as
`611fb96ff`.  Separate serialized builds of
`+FabiusFunction.OriginalUniqueness` (3244 jobs) and
`+FabiusFunction.LegendreSeriesConvergence` (2715 jobs) both exited 0 without
warnings.  Both paths and the codexbox token are released; no public API,
import, facade, root, or document changed.

### `codex/fabius-theorem-polish-20260825`

The prior task is complete and its complete source tranche is integrated on
current `main` through `301a46561`.  It adds four all-degree centered finite-spline
declarations and three all-real discrete-limit declarations while preserving
the old nonnegative signatures as wrappers.  Independent theorem/API review
found no blocker.  At immutable merge `60458909a`, serialized builds of
`+FabiusFunction.FabiusUniformSpline`,
`+FabiusFunction.FabiusDiscreteLimitIntegration`,
`+FabiusFunction.FabiusComputability`, and
`+FabiusFunction.PaperFabiusAsymptotic` all exited 0.  Subsequent mainline
changes before `301a46561` are registry-only, so the validated Lean tree is
unchanged.  The source lease is released; this branch may begin a new ordinary,
nonoverlapping claim under the shared protocol.

The four-file claim advertised at `ca387fea0` is implemented by source
checkpoint `87c9b00f4` for exactly:

- `Lean/FabiusFunction/NegativeLaplace.lean`;
- `Lean/FabiusFunction/LaplaceMoments.lean`;
- `Lean/FabiusFunction/NegativeLaplaceDerivatives.lean`; and
- `Lean/FabiusFunction/NegativeLaplaceVertical.lean`.

The follow-on claim at `a6091bacf` adds only
`Lean/FabiusFunction/LaplaceMomentBounds.lean`; source checkpoint `efee2a7e1`
extends normalized-moment nonnegativity to every real tilt and intentionally
depends on the four-file tranche's all-real zeroth-moment theorem.  Registry
checkpoints `1d4a88a42` and `5331c74d5` report both tranches, and `909cb359c`
froze further work pending coordinator disposition.  Independent review found
no truth, API, dependency, duplicate, or scope blocker.  Coordinator merge
`0d308188c` then exposed one elaboration-only mismatch in the new global
`ContDiff` proof; `c4bc42f16` fixes it by changing the goal explicitly to the
pointwise quotient before applying `ContDiff.div`, without changing any public
statement.

At the repaired immutable tree, the derivative, vertical, bounds, and
`PaperFabiusAsymptotic` targets all exit 0; the two upstream focused targets
also exit 0 with source blobs unchanged by the repair.  Exact job counts and
the one superseded failed attempt are recorded in the build log and branch
registry.  The five source leases are released.  The branch may begin another
ordinary nonoverlapping claim after reading this board; no EVO validation token
is granted.

Source commit `0f7d53e8c` is a separate two-path unit in
`FabiusDiscreteLimitToeplitz.lean` and
`FabiusDiscreteLimitIntegration.lean`.  It adds eight finite-depth value,
nonconstancy, shift-difference, and outer-index-one comparison results.  Two
independent reviews found the mathematics, domains, indexing, `RCLike`
transport, API, placement, imports, duplicates, and scope green.  The
coordinator cherry-picked only that source as `de8707b44`.

The first Toeplitz build exposed proof elaboration defects in the two concrete
natural-floor evaluations and final generic-field normalization; it grants no
validation evidence.  Repair `8e09c4d98` supplies explicit `Nat.floor_eq_iff`
witnesses and `push_cast` before `ring`, changing no public statement.  At that
repaired immutable tree, serialized `LAKE_JOBS=1` builds of
`+FabiusFunction.FabiusDiscreteLimitToeplitz` (3320 jobs) and
`+FabiusFunction.FabiusDiscreteLimitIntegration` (3422 jobs) both exit 0 with
no warnings.  The two source leases are released; the branch may sync and
begin a new ordinary nonoverlapping claim, but receives no build token.

Synchronized registry tip `3102741f2` correctly records that acceptance.  Its
request for human-readable counterparts to the eight new declarations is a
frontier-document backlog item, not a renewed theorem-polish document lease.
The designated frontier successor may advertise that mapping as a later,
separate source phase only after the current three-hunk source/PDF disposition;
do not fold it into the narrowly granted checkpoint above.

Source commit `665b6bce` is a later one-file
`ProbabilityLaplaceMoments.lean` tranche.  It adds the generic restricted-law
reflection identity, the all-degree signed binomial transform for unit
Laplace moments, and its Fabius specialization while preserving the existing
zero-degree theorem as a compatibility wrapper.  Two independent reviews
accept the reflection orientation, signs, indices, hypotheses, API,
dependency placement, and duplicate scan.  The coordinator integrated the
exact source as `c80f61c90`.  Its first focused build exposed only recursive
`simp` use of bare `neg_pow` in the local binomial expansion and supplies no
validation evidence.  Repair `6b6757e90` names the single intended
`(-x)^j` identity explicitly, changing no theorem statement, formula, import,
or public API.  At that repaired tree,
`LAKE_JOBS=1 lake build +FabiusFunction.ProbabilityLaplaceMoments` completed
3187 jobs in 18 seconds and exited 0 without warnings.  The source lease is
released; this branch has no document or build token.

Registry-first claim `4267605f0` then advertised a disjoint normalized
reflection follow-up in the same released module.  Exact source commit
`493575690` replaces the direct `LaplaceMoments` import with the acyclic
`NegativeLaplaceDerivatives` import and adds exactly
`normalizedLaplaceMoment_reflection`,
`normalizedLaplaceMoment_one_complement`,
`normalizedLaplaceMoment_one_sub_half_odd`, and
`negativeLaplaceLogSecond_even`.  Independent exact review accepts the signed
binomial cancellation, degree-one complement, oddness/evenness orientations,
degree-two variance algebra, imports, API, and duplicate scan.  The
coordinator integrated it as `853a09a80`.  A serialized
`+FabiusFunction.ProbabilityLaplaceMoments` build completed 3188 jobs and exited
0, reporting only one nonblocking `unnecessarySimpa` linter in the new
reflection proof.  The source lease and codexbox token are released; no
document, facade, or root path changed.

Registry-only claim `8c6456646` advertises an ordinary two-source compact
Lambert-W obstruction tranche in `FabiusWikipediaMain.lean` and
`FabiusSharpAsymptotic.lean`.  Its six names are
`fabiusWikipediaLambertMain`,
`fabiusCorrectedWikipediaMain_eq_WikipediaLambertMain_add`,
`isEquivalent_exp_iff_tendsto_log_sub`,
`log_fabius_sub_WikipediaLambertMain_not_tendsto_zero`,
`log_fabius_sub_WikipediaLambertMain_not_isBigO`, and
`fabius_not_isEquivalent_exp_WikipediaLambertMain`.  Three independent
preflights accept the exact 2022 online formula, lower-Lambert phase,
`+ negativeLaplacePsi` sign, log-ratio iff under eventual positivity,
nonvanishing/Big-O obstruction chain, import topology, current preimages, and
collision scan.  Source work may proceed in exactly those two Lean files plus
the own registry, preserving every old header/import; no build token is granted
before an immutable reviewed source handoff.  The later minimal gate is
`+FabiusFunction.FabiusSharpAsymptotic`.  Any Fourier explanation must state
`Gamma(1-χ_k) = -χ_k Gamma(-χ_k)` only for `k ≠ 0`, with the zero mode handled
separately, and the six declarations formally refute multiplier one rather
than every arbitrary multiplier.  No document path is owned by this claim.

Exact source `b0600193b` now implements all six declarations in exactly those
two files; handoff `20751d800` freezes result blobs `61ae4480f` and
`e6939d6e8`.  Two independent actual-diff reviews accept the formula, totalized
definition, plus sign, arbitrary-filter log-ratio iff, residual subtraction,
Big-O implication, positive-side domain, imports, API compatibility, current
preimages, and collision scan.  The coordinator integrated only that immutable
source as `8d928a55f`.  At the resulting exact tree, the sole serialized
command

```text
LAKE_JOBS=1 lake build +FabiusFunction.FabiusSharpAsymptotic
```

completed 3891 jobs and exited 0.  Its only diagnostic was the inherited
nonblocking `unnecessarySimpa` linter in `ProbabilityLaplaceMoments.lean`.
Both Lean source paths and both host Lean/Lake tokens are released.

**Completed relaxed primary-document handoff.**  Commit `2546fe21b`
changes exactly the canonical primary TeX/PDF pair, and handoff `581da767f`
changes only the branch registry; synchronized tip `81dc71554` preserves the
accepted blobs.  Three independent reviews accept the compact MSE formula,
lower-Lambert branch, `+ negativeLaplacePsi` sign, positive-side domain, all
six Lean mappings, multiplier-one-only limitation, exact source ancestry, and
collision-free labels/references/citations.  The final TeX blob is
`5071d1f32f5f732e7cc59f569190532b6d815d57`, SHA-256
`D36680516B8F73CAE3B4237477A8B04803A5ED5EBDFA741A86CA6BE7CEA4C2DD`;
the matching PDF blob is `4529d9c453d647e4068e2ff5527c417f5564f5d0`,
SHA-256 `FA8DAF5CB82DEFB7E807A09EF6FBA43C48C4E312862ACAFC7BDE36340EC36C51`,
1,018,335 bytes and 59 A4 pages.

The worker's three sequential sidecar `pdflatex` passes exited 0 and produced
57, 59, and 59 pages.  The final pass was settled with no undefined
reference/citation, rerun, changed-label, fatal/LaTeX-error, overfull-box, or
rendered-`??` diagnostic; all fonts are embedded, and the sole underfull
warning is inherited from an unchanged module-map cell.  Independent static,
text, font, and raster audits passed.  The worker inspected pages 1--3 and
50--59; coordinator review additionally covered cross-reference-only changes
on pages 4 and 45, both clean.  No further rebuild is required.

The coordinator integrated the atomic TeX/PDF pair as `260d66fce` and
appended only the final 103-line release block from the worker registry as
`ff41c127a`, retaining the canonical coordinator-extracted registry history
rather than importing the feature's long historical registry.  The primary
document lease and EVO TeX/PDF stream are released.  No document owner or TeX
stream remains; every canonical document path is frozen pending a later board
grant.

The later three-source exact cluster-set tranche consists of source commits
`305d71e3f` (`FabiusWikipediaMain.lean`), `46a8e3d8f`
(`FabiusWikipediaObstruction.lean`), and `ba7eebad0`
(`FabiusSharpAsymptotic.lean`).  Three independent static audits accept all 25
new documented declarations, the exact range/cluster-set transport,
liminf/limsup orientations, strict periodic gap, no-arbitrary-constant result,
API preservation, import topology, exact preimages, and collision scan.  The
coordinator integrated those isolated commits in order as `0e283d01f`,
`9830baf09`, and `508341204`, excluding both registry-only checkpoints and the
moving feature history.

The first focused Sharp build exposed only elaboration-normal-form defects in
the final module and supplies no validation evidence.  Statement-preserving
repair `e332a58fd` types the constant comparison in `Real`, unfolds composed
and pointwise-added functions at function level, passes `IsLeast`/`IsGreatest`
membership proofs with their comparison points implicit, and removes the one
new unused simp argument.  At that repaired tree,
`+FabiusFunction.FabiusSharpAsymptotic` completed 3891 jobs and exited 0.
Fresh downstream builds of `+FabiusFunction.FabiusInverseAsymptotic` (3931
jobs) and `+FabiusFunction.PaperFabiusAsymptotic` (3960 jobs) also exited 0;
only the inherited `ProbabilityLaplaceMoments.lean` linter appeared.  All
three source paths and both host tokens are released.  This source extension
does not reactivate the completed primary-document lease; canonical documents
remain frozen.

### `codex/fabius-effective-bounds-20260825`

Registry-only claim `bc14ab696` is approved for exactly
`Lean/FabiusFunction/FabiusLambertRates.lean` plus its own registry.  The six
advertised declarations are `eventually_le_dyadicLambertPhase`,
`dyadicLambertPhase_isEquivalent_id`,
`dyadicLambertPhase_inv_isEquivalent_inv`,
`smallArgumentLog_inv_isTheta`,
`isBigO_lambertScale_iff_smallArgument_log`, and
`isLittleO_lambertScale_iff_smallArgument_log`.  Independent review finds the
module/dependency blobs unchanged from the claim base, no competing path or
semantic duplicate, and the proposed equivalence chain mathematically and
topologically sound for an arbitrary normed codomain.  The first result must
be described only as an *eventual* inequality; it supplies no explicit
numerical cutoff.

Exact source commit `a8421fd7f` was integrated as `5fbdf6139`.  The first
`+FabiusFunction.FabiusLambertRates` attempt exposed only failure to eta-reduce
Mathlib's pointwise reciprocal functions and supplies no validation evidence.
Statement-preserving repair `2a5be17f3` changes the proof to an explicit
definitional `change`.  At the repaired tree, separate serialized builds of
`+FabiusFunction.FabiusLambertRates` (3252 jobs) and its narrow direct consumer
`+FabiusFunction.FabiusSharpAsymptoticTransfer` (3341 jobs) both exited 0
without warnings.  Existing headers remain unchanged; the first tranche's
source lease and codexbox token are released.

Registry-only follow-on `f3f9785fe` claims exactly
`Lean/FabiusFunction/FabiusSaddleReferenceTail.lean` plus its own registry.  It
proposes public `exp_neg_sq_centralRadius_div_four`,
`integral_norm_gaussian_add_oddCorrection_standardRadius_le_inv_pow_eight`,
and
`integral_norm_gaussian_add_oddCorrection_standardRadius_isBigO_inv_pow_eight`,
while preserving the existing order-one Big-O theorem header as a wrapper.
Independent review verifies the standard-radius identity, constant arithmetic,
coefficient hypotheses, arbitrary-filter transport, current-main preimage,
and lack of competing active path claim.  Two corrections are binding:

- call the result the exposed **coarse eighth-order algebraic rate**, not a
  sharp rate; the Gaussian decay and the retained `1/A` factor are stronger;
- record the downstream private
  `exp_neg_sq_orderRadius_div_four` all-orders identity as known nonblocking
  semantic overlap rather than claiming no semantic match.

Exact source commit `933121538` implements the claim and was integrated as
`f85409a18`.  Three independent reviews accept the identity, constants, signs,
threshold, arbitrary-filter packaging, and weakening from `O(b⁻⁸)` to
`O(b⁻¹)`.  The source has the exact current-main preimage, changes only the
claimed module, and promotes the former private identity while adding the two
advertised estimates.  The old order-one Big-O theorem header and both direct
consumer interfaces remain byte-identical.  The prose correctly calls the rate
coarse and records the discarded `1/A` factor and downstream private overlap.
Separate serialized builds of `+FabiusFunction.FabiusSaddleReferenceTail`
(3432 jobs) and `+FabiusFunction.GaussianPolynomialTail` (3436 jobs) both exited
0 without warnings.  The source lease and codexbox token are released;
`FabiusLambertRates.lean` was not changed by this tranche.

Registry-first claim `0cf2a0df0` advertises a disjoint ordinary follow-up in
`QuantitativeSaddle.lean`.  It will add
`norm_normalized_integral_sub_reference_le_of_L1` and
`norm_normalized_integral_sub_one_le_of_L1`, exposing the exact pointwise
Gaussian-normalized `L¹` estimate already embedded in the generic filter-level
proof.  It may refactor the proof of
`normalized_integral_sub_reference_isBigO_of_L1`, but that theorem's header and
every other public header must remain exact.  Independent preflight accepts the
normalization constant, positivity, integrability hypotheses, mass
specialization, imports, naming, and duplicate scan.  The inactive serialized
proposal to relocate `norm_standardGaussian` is explicitly excluded, as are
all imports, facades, root files, and documents.  Exact source commit
`24f1eee30` implements the two declarations and proof-only Big-O refactor in
exactly that one module and is integrated as `caed8800e`.  Independent exact
review accepts the normalization, integrability hypotheses, mass
specialization, arbitrary-filter refactor, imports, compatibility, and absence
of a duplicate.  Separate serialized builds of
`+FabiusFunction.QuantitativeSaddle` (2782 jobs) and its direct API consumer
`+FabiusFunction.SaddleAllOrders` (2783 jobs) both exited 0 without warnings.
The path and codexbox token are released.

Registry-first claim `90432f3c6` advertises a further disjoint ordinary
one-file tranche in `UnitLaplaceMomentBounds.lean`.  It proposes
`unitLaplaceMoment_tilt_bounds`, `unitLaplaceMoment_pos_iff`,
`fabiusLaplaceMoment_tilt_bounds`, and `fabiusLaplaceMoment_pos_all` while
preserving every existing header and import.  Preflight accepts the two-sided
comparison with factors `exp (min (t - s) 0)` and
`exp (max (t - s) 0)`, positivity transport, the half-moment specialization,
placement, imports, and duplicate scan; `fabiusLaplaceMoment_zero_pos_all` is
only its degree-zero special case.  Exact source commit `d9598f3b6` now
implements the four declarations in the claimed module and is integrated as
`7b892b41c`.  Two independent reviews accept the sign cases, endpoint behavior,
positivity equivalence, half-moment specialization, exact preimage, imports,
and API preservation.  Separate serialized builds of
`+FabiusFunction.UnitLaplaceMomentBounds` (3189 jobs) and its sole direct
importer `+FabiusFunction.LaplaceMomentBounds` (3417 jobs) both exited 0.  They
reported only the already-recorded nonblocking `unnecessarySimpa` linter from
`ProbabilityLaplaceMoments.lean`.  The path and codexbox token are released;
no document, facade, root, import, or other path was changed.

Registry claim `96e05f698`, corrected before source work by `ca227c69e`,
advertises one ordinary tranche in `FabiusLambertAllOrderAlgebra.lean`.  It will
add `dyadicLambertDisplacementPolynomial_natDegree`, proving degree
`max n 1`, and
`dyadicLambertDisplacementPolynomial_leadingCoeff_succ`, with right-hand side
`(-1 : ℝ)^n * (n + 1 : ℝ)⁻¹ * ((Real.log 2)⁻¹)^(n + 2)`.  Two independent
preflights accept the unique `j = 0` highest-degree summand, signs, powers,
noncancellation, imports, placement, preimage, and duplicate scan.  The scalar
leading-coefficient recurrence is valid only for `n ≥ 1`; `n = 0` has the
separate empty-convolution base `L₁ = (log 2)⁻²`.  Source work may proceed only
in that Lean file plus the own registry, using private proof helpers and
preserving every old header.  No build token or document/facade/root lease is
granted.  After an immutable reviewed handoff, the intended serialized gates
are `+FabiusFunction.FabiusLambertAllOrderAlgebra` and then its sole direct
importer `+FabiusFunction.FabiusLambertFormalLog`.

Exact source `8f47687e5` and handoff `3e17e4e48` implement that complete
two-name claim in the sole module, with result blob `08e5a2d9475746a517d8d835b699c00d8c00c0a9`.
Three independent static audits accept the degree bound, exceptional empty
base, positive-index unique top summand, closed leading coefficient, imports,
API, exact preimage, and collision scan.  The coordinator integrated only the
source as `5cc6970fd`.  Its first focused build exposed five elaboration-only
normal-form failures and supplies no validation evidence: the two successor
case targets were already normalized, the natural casts in the head coefficient
were opaque to `ring`, the positivity of a `Fin.succ` value did not unfold, and
the coefficient of the head-plus-tail polynomial had not distributed over
addition.

Statement-preserving repair `128890b71` removes the two redundant rewrites,
uses explicit `push_cast` and the target's cast shape, proves the successor
positivity directly, and adds `Polynomial.coeff_add` before the finite-sum
coefficient rewrite.  Independent post-fix review accepts that exact repair.
At the repaired immutable tree, separate serialized builds of
`+FabiusFunction.FabiusLambertAllOrderAlgebra` (3249 jobs) and
`+FabiusFunction.FabiusLambertFormalLog` (3253 jobs) both exited 0 without
warnings.  The source path and codexbox token are released; the corrected
`n >= 1` recurrence qualification remains binding for future prose.

Registry claim `02c913b2d`, exact source `caf654097`, and handoff `fd53d0928`
then strengthen `LaplaceMomentBounds.lean` with
`fabiusLaplaceMoment_strictAnti` and `normalizedLaplaceMoment_pos_all`.
Independent review accepts the derivative-sign argument, strict-order
orientation, quotient positivity at every degree and real tilt, exact preimage
and result blob `007c2ed04697ab56d3fd0654da477d32d360a61b`, imports, and collision scan.
Both established nonnegativity lemma headers remain textually exact as
compatibility consequences, with the deliberately retained positive-scale
hypothesis confined under a declaration-local linter scope.  The coordinator
integrated only the isolated source as `63e7334ec`.  A serialized build of
`+FabiusFunction.LaplaceMomentBounds` (3417 jobs) exited 0, and the later
shared downstream `+FabiusFunction.NegativeLaplaceDerivativeBounds` gate
(3419 jobs) also exited 0.  Both reported only the inherited nonblocking
`ProbabilityLaplaceMoments.lean` linter.  This source path and the codexbox
token are released.

Registry claim `7bba02fea`, exact source `d07e8ad3b`, and handoff `295c75b93`
globalize the normalized cumulant-polynomial differential chain in
`NegativeLaplaceDerivatives.lean`: the three new `_all` theorems prove
`kappa_1' = kappa_2`, `kappa_2' = kappa_3`, and `kappa_3' = kappa_4` at every
real tilt.  Three independent reviews accept every sign and coefficient,
including the third-order function-equality transport, exact result blob
`80f3e80c1e9777405499a50da808bef5c71fa372`, import topology, collision scan,
and the distinction between global cumulant algebra and the still-positive
domain for identifying it with derivatives of `negativeLaplaceLog`.  All
three old positive-scale theorem headers remain byte-exact wrappers, with
their retained hypotheses under declaration-local linter scopes.  The
coordinator integrated only the isolated source as `5100bc049`, after the
strict-moment source rather than inheriting the moving branch history.  A
serialized build of `+FabiusFunction.NegativeLaplaceDerivatives` (2858 jobs)
exited 0, followed by the shared downstream
`+FabiusFunction.NegativeLaplaceDerivativeBounds` build (3419 jobs), also exit
0; only the inherited linter appeared.  The source path and codexbox token are
released.  No document, facade, root, import, or other path is granted by
either tranche.

Exact source `51b9ad393` is a subsequent one-file binary-reduction sharpening.
It exposes the all-real positive-index constant-three estimate, retains both
old constant-four headers as wrappers, and replaces the private local Fabius
bound with the canonical `Regularity` API through an explicit acyclic import.
Independent review accepts the essential `1 ≤ m` edge, exact sum-of-residuals
constant, `m = 1` and nonpositive-input cases, imports, API, preimage, and
collision scan.  The coordinator integrated only that source as `942fd6b68`.
Separate serialized builds of `+FabiusFunction.FabiusBinaryReductionSeries`
(2820 jobs) and `+FabiusFunction.FabiusGlobalQBinomialSeries` (3324 jobs) both
exited 0 without warnings.  The path and codexbox token are released.

### `codex/fabius-inverse-asymptotic-20260825`

The staged inverse-asymptotic handoff is accepted by exact source, not by
merging its feature ancestry.  Generic source `9b7affe68` adds
`quadratic_asymptotic_inversion` in the new
`QuadraticAsymptoticInversion.lean`; endpoint source `6ee65a167` adds the three
totalized inverse main terms and five left/right endpoint theorems in the new
`FabiusInverseAsymptotic.lean`; facade source `d6464f6c8` adds exactly the
endpoint import and accurate prose to `PaperFabiusAsymptotic.lean`.
Independent reviews accept the quadratic rationalization, affine sign,
`O(log T / sqrt T)` rate, lower-Lambert specialization, logarithmic constant,
explicit prefactor, reflection transport, one-sided filters, totalization,
imports, public surface, and collision scan.

The coordinator integrated those sources as `431425975`, `18e7c6dcf`, and
`504ed4892`.  Initial focused attempts exposed only function/Pi normal forms,
one missing `Topology` scope, one square-root identity presentation, explicit
`Iio` membership, and an ambiguous facade pronoun that incorrectly appeared
to refer to the Lambert phase; they supply no validation evidence.  Repairs
`863954b6a` and `6d5a6c09c` preserve every theorem statement and make the
facade say explicitly that `Real.log (fabiusInv F hF y)` has the stated main
term.  Serialized builds of
`+FabiusFunction.QuadraticAsymptoticInversion` (2011 jobs),
`+FabiusFunction.FabiusInverseAsymptotic` (3931 jobs), and
`+FabiusFunction.PaperFabiusAsymptotic` (3960 jobs) all exited 0.  After the
later Sharp cluster-set integration, the latter two were rerun on the final
cumulative tree and again exited 0 with the same job counts; only the inherited
`ProbabilityLaplaceMoments.lean` linter appeared.  All three source paths and
the requested EVO token are released.  No TeX/PDF, root aggregate, or
canonical-document path was requested or changed.

### `codex/fabius-shifted-prefix-grid`

The one-file source claim is implemented at checkpoint
`00ff41a5e` in `Lean/FabiusFunction/ThueMorseGenerating.lean`.  It adds the
generic `shiftedPrefixGridValue` family and seven APIs, while preserving the
two public grid definitions and all eight legacy theorem headers and
attributes as compatibility wrappers.  Independent exact source review is
green: the seven declarations are true, the zero/one simp bridges are safe,
the positive-level hypothesis is necessary, every old type and attribute is
unchanged, and no duplicate or competing source claim exists.

The branch then expanded beyond its branch-specific “source file plus own
registry” grant and committed `docs/PAPER_COVERAGE.md` at `dcd5f8a06`.  Preserve
that feature commit for separate review; it was not authorized for `main` by
the registry-first self-claim alone.  Commit `faf1fcaf6` similarly changed
`docs/AUDIT_FINDINGS.md` 53 seconds before checkpoint `148990f0a` explicitly
serialized both files, but still exceeded the earlier exact branch grant.
Pathwise audit nevertheless finds both documentation deltas accurate, so the
coordinator now explicitly accepts them as separate units rather than
discarding useful work.  This is not permission for another expansion.

Feature tip `8ea040921` was clean, synchronized with `148990f0a`, and froze all
prior paths.  Coordinator merge `ae16882d5` integrates that frozen tip.  The
registry now correctly identifies SHA-256 `48C94725...` as the audit patch
hash, not the committed file hash (`507136BA...`, Git blob `3eeb0880...`), and
the coverage map records the immutable validation evidence.

At `ae16882d5`, serialized builds of `+FabiusFunction.ThueMorseGenerating`
(2085 jobs), `+FabiusFunction.ThueMorseApproximation` (3307 jobs),
`+FabiusFunction.ThueMorseExponential` (2086 jobs), and
`+FabiusFunction.PaperKFoldThueMorse` (3327 jobs) all exited 0.  The source
lease is released, while `PAPER_COVERAGE.md` and `AUDIT_FINDINGS.md` return to
campaign-wide serialized status.  The branch may begin a new ordinary,
nonoverlapping claim after reading this board; no EVO build token is granted.

The later finite-jet source checkpoint `51af7f7e1` changes exactly
`ThueMorseGenerating.lean` and `ThueMorseApproximation.lean`.  It adds the
generic finite-block/right-convolution coefficient bridge, its independent
block-depth/prefix-order specialization, and
`iteratedPrefix_eq_approximationPolynomial_coeff_all`; the old positive-order
theorem remains type- and attribute-identical as a wrapper.  Two independent
reviews found the cutoff, zero-order case, indexing, placement, API,
duplicates, imports, and scope green.  The coordinator cherry-picked only that
two-file source unit as `62ab80d03`, excluding the later speculative registry
history, and ran four serialized `LAKE_JOBS=1` targets:

- `+FabiusFunction.ThueMorseGenerating` (2085 jobs);
- `+FabiusFunction.ThueMorseApproximation` (3307 jobs);
- `+FabiusFunction.ThueMorseExponential` (2086 jobs); and
- `+FabiusFunction.PaperKFoldThueMorse` (3327 jobs).

All exited 0.  The Approximation target and facade report two nonblocking
linters: an unnecessary `simpa`, and the intentionally retained compatibility
binder `hk` is not referenced by the wrapper proof.  The two source paths are
released to this branch's already-advertised all-order same-path refinement
after it fetches/merges the new main.  Before the next source edit, correct the
worker registry's Generating evidence: the actual Git blob is `2908f1f1652e`
and content SHA-256 is
`04F8F9AB915928A98FC422C3A5048C53110FD67C29007CE55483A853561A8D9C`,
not the recorded `2412e544b` / `499A7D...`.  No build token or campaign-wide
document lease is granted for the follow-up.

Comment-only source commit `ef2430205` corrects two guide-level descriptions:
the infinite-product notation is a coefficientwise finite stabilization, and
the order-zero cutoff admits only index zero rather than making the series
one-term.  Mechanical comparison proves that every byte outside the two
leading module comments is unchanged; the coordinator integrated this exact
commit as `5d779327a`, so no Lean build is required for that prose-only unit.

The branch's ordinary claim covered exactly three source paths:
`FabiusQBinomialTaylor.lean`, `ThueMorseGenerating.lean`, and
`ThueMorseApproximation.lean`.  The seven declarations are
the four translated-power-sum Appell APIs
`thueMorseTranslatedPowerSumPolynomial_comp_X_add_C`,
`thueMorseTranslatedPowerSumPolynomial_hasseDeriv`,
`thueMorseTranslatedPowerSumPolynomial_derivative`, and
`thueMorseTranslatedPowerSumPolynomial_derivative_succ`, plus
`one_sub_X_pow_mul_approximationPolynomialInt_all`,
`thueMorseBlockPolynomial_mul_invOneSubPow_eq_approximationPolynomialInt`, and
`correctedPrefixCoefficient_eq_stepApproximant_all`.  No competing path or
plausible-name claim was found.  The earlier convolution bridges and
`iteratedPrefix_eq_approximationPolynomial_coeff_all` are already integrated
and compiled context; do not reimplement them.  The corrected Generating blob
evidence is `2908f1f1652e` / SHA-256 `04F8F9AB...A8D9C`.

Source commit `8021c555f` implements the four Appell declarations in
`FabiusQBinomialTaylor.lean`; its parent matches main blob `4032b5184` and its
result blob is `52492287b`.  Two independent reviews accept the finite
translation law, total Hasse law, derivative specializations, every boundary
case, imports, API, placement, and duplicate scan.

Source commit `f7152d5fc` independently implements the three total
approximation declarations in `ThueMorseApproximation.lean`; its parent matches
main blob `87023172f` and its result blob is `d2e85228f`.  Two independent
reviews accept the polynomial and formal-series identities at `k = 0`, the
case-free coefficient and normalized-step bridges, the strict cutoff, private
helper deletion, and exact preservation of all old public wrapper headers and
attributes.  Registry tip `b52fa523e` freezes both source units on a branch
already synchronized through main `99b67cf5b`.

**EVO validation grant.**  This branch now holds the sole EVO token.  From a
clean pushed tree, merge this coordinator checkpoint, verify that the two
source blobs remain exactly `52492287b` and `d2e85228f`, and run these as three
separate sequential invocations with `LAKE_JOBS=1`:

```text
lake build +FabiusFunction.FabiusQBinomialTaylor
lake build +FabiusFunction.ThueMorseApproximation
lake build +FabiusFunction.PaperKFoldThueMorse
```

Do not run them in parallel and run no additional Lean/Lake/TeX/PDF target.  If
one fails, do not run the later targets or edit source under the same token;
record the complete first failure in the own registry, push, and stop.  If all
three pass, record exact SHA/tree, commands, job counts, warnings, and exits in
the own registry, push, and stop for coordinator integration.  Never push
`main`.

**Validation and integration result.**  Registry checkpoint `b28da9013`
records the completed EVO run at exact merge `4367a7f86`, tree `db635e6a073b`.
The three required separate `LAKE_JOBS=1` targets completed in order:

- `+FabiusFunction.FabiusQBinomialTaylor`: 3320 jobs, exit 0, no warnings;
- `+FabiusFunction.ThueMorseApproximation`: 3307 jobs, exit 0, only the two
  known unused-`hk` compatibility linters;
- `+FabiusFunction.PaperKFoldThueMorse`: 3327 jobs, exit 0, replaying only
  those two linters.

No later source edit occurred.  The coordinator integrated only exact source
commit `8021c555f` as `30cc17175`, then exact source commit `f7152d5fc` as
`ca3a0dca5`; the divergent feature history and registry were not merged.
Every claimed source path and the EVO token are released.  The branch may sync
and begin a new ordinary nonoverlapping claim, but has no current source or
build ownership.

Registry-first claim `cb51e8fb5` advertises a new, disjoint three-source
tranche in `DyadicClosedForm.lean`, `ThueMorsePrefix.lean`, and
`FabiusRawQBinomialFormula.lean`.  It will relocate the existing public
`thueMorseSign_dyadic_complement` upstream without changing its header or
attributes, and add `iteratedPrefix_dyadic_reverse_window` plus
`iteratedPrefix_dyadic_reverse_window_eq_zero_iff`.  Read-only preflight accepts
the signed reflection formula, edge cases, import direction, consumer path,
and absence of a competing declaration.  Exact source commit `d887c8101`
relocates the complete complement theorem block byte-for-byte and adds the two
advertised Prefix theorems; registry checkpoint `66a4961d2` records exact blobs
and a clean current-main merge.  Two independent source audits accept every
saturated-subtraction edge case, both induction dimensions, zero-locus
cancellation, imports, API, and consumer topology.  The coordinator integrated
only the exact source as `f66ef224b`.  Separate serialized builds of
`+FabiusFunction.ThueMorsePrefix` (2019 jobs) and
`+FabiusFunction.FabiusRawQBinomialFormula` (3319 jobs) both exited 0 without
warnings.  All three source paths and the codexbox token are released.  The
former future request is dispositioned by the bounded grant below.

**Released documentation request.**  Registry request `b6ebc310c` passed two
independent semantic/collision audits and was briefly granted the exact
coverage/primary/walkthrough paths above.  The user has now clarified that no
documentation-owner agent is active.  The grant and EVO TeX/PDF stream are
therefore released before any canonical document edit or render.  At pushed
feature tip `059b45ed5`, none of the five formerly granted canonical paths
differs from `main`; only the branch's own registry preserves the request and
its superseded acceptance.
`PAPER_COVERAGE.md`, both primary files, and both walkthrough files return to
the frozen pool.  The signed-reciprocity mapping remains a documentation
backlog item and gives this branch no continuing ownership.

The branch later published preservation checkpoint `f67446278` and release
checkpoint `9c2f38c07` from the board state it had already merged.  This was a
synchronization race: the requested five-path scope had been authorized in
that merged board, but current main had released it 43 seconds before the
branch-side acceptance.  Independent content audit accepts the signed formula,
zero iff, declaration mapping, boundary/run distinctions, coverage update,
walkthrough module row, static TeX predicates, and both rendered artifacts.
It is nevertheless not an integration base.  Its primary pair starts from the
old pre-Lambert TeX/PDF and would erase the accepted compact-Lambert section;
the PDFs conflict and must never be selected or combined.  Preserve the remote
checkpoint, but merge none of its moving history.  The coverage and walkthrough
units may be reconsidered later, while the disjoint primary textual hunks need
a fresh exact-path document grant and a newly rebuilt matching PDF.  No such
grant is active; all five paths remain frozen.

### `codex/fabius-exposition-integration`

Checkpoint `5e0505bf2` was merged to `main` by `ccf81cf83` while the
documentation freeze was active.  Its later merge at `1570b29b9` contributes
only `docs/registry/codex-fabius-exposition-integration.md` relative to the
coordinator checkpoint; it does not change an exposition or frontier artifact.
That registry's useful audit body is retained, while its `cffe24808` snapshot
and expired current-tree/page-count statements are now labeled explicitly.

**Former single-owner frontier lease.**  The staged frontier work had spanned
only:

- `docs/non-formalized-research-frontiers/README.md`;
- `docs/non-formalized-research-frontiers/non-formalized-research-frontiers.tex`;
- its matching `.pdf`; and
- `docs/registry/codex-fabius-exposition-integration.md`.

Stage-one source checkpoint `78260751f` and the audit correction
`23daad436` are pushed; feature tip `e1c087738` is clean and synchronized with
current main `ba2be1b78`.  Its net delta remains exactly the frontier
README/TeX and the branch registry; the committed PDF blob is still identical
to main.  Independent audit accepts the mathematical/formalization boundary,
six-part structure, donor clusters, provenance, labels/references/citations,
gap register, and all four required corrections.  In particular the corrected
TeX SHA-256 is
`8562CF91CDB48132C1DBF127B80886D9EFF8D46057805A200B4579A42E054546`;
the running-head reset occurs once, the removed probability-product label
occurs zero times, both canonical labels occur once, and the two open-ledger
implementation routes are restored.  Static audit reports 986 unique labels,
625 resolved references, 52 unique bibliography keys, 20 resolved citation
targets, 1201 balanced environment pairs, 20 candidates, 20 obligations, and
seven parts; `git diff --check` is green and no path is unmerged.

**Stage-two result.**  The branch merged this board cleanly at `1ca2a09be`
without changing the accepted TeX, then ran exactly the three authorized
sequential `pdflatex` passes with a fresh `_stage2` job name.  All exited 0;
page counts were 178, 186, and 186.  The third pass settled every reference and
citation and reported no duplicate label, horizontal overfull box, rerun,
changed-label, fatal, or LaTeX-error diagnostic.  It did report exactly one
`Overfull \\vbox (59.28255pt too high)` immediately before output page 184.
The worker correctly stopped without a fourth pass, TeX/README edit, canonical
PDF replacement, or primary cleanup.  Checkpoint `e6ac85e2f` records the exact
evidence; the rejected PDF and log remain sidecar-preserved under `_stage2`.
No validation claim or PDF acceptance is made from that run, and its EVO tool
token is released.

**Narrow source-repair result.**  After merging the repair directive cleanly,
source commit `5fee1bb90` changes exactly one locally scoped token in the
single indivisible formal-background `tabularx`: `\\small` becomes
`\\footnotesize` inside its existing group.  The preserved log/PDF show that
this table was deferred from page 183 and exceeded a fresh page 184 by
59.28255pt; shrinking roughly sixty local baselines directly addresses that
measured excess.  No row, prose, mathematics, status, label, reference,
citation, environment, README, PDF, or global typography changes.  The new
TeX SHA-256 is
`D6791ED6AA0246EE9986D67BDF0BCC9823D431E46CAEA1FEE34409FEB25D16DA`.
Checkpoint `87bf890d3` is clean, records unchanged static predicates, and is
independently accepted for a fresh build.

**Stage-three grant.**  This branch again holds the sole EVO tool token for the
canonical frontier only.  From clean tip `87bf890d3`, use a fresh
`non-formalized-research-frontiers_stage3` job name and run exactly three
sequential invocations of the same recorded `pdflatex` command.  Run no Lean,
Lake, `latexmk`, other TeX compiler, or fourth pass.  The third pass must have
settled references/citations, zero rerun or changed-label diagnostics, zero
duplicate labels, zero overfull horizontal **and vertical** boxes, and no
fatal/LaTeX error.  After the third pass only, read-only `pdfinfo`, `pdffonts`,
text extraction, and page rasterization are permitted for validation.  Require
all fonts embedded; inspect page 184 for table legibility, clipping, footer
collision, and surrounding page breaks, and recheck page 10 plus every changed
semantic cluster.

If every gate passes, replace the canonical frontier PDF with the exact settled
stage-three bytes, record the three commands/exits/page counts, log/PDF hashes
and sizes, all diagnostic counts, font/text/raster evidence, visual inspection,
Git blob, and clean status in the branch registry, then commit only that PDF
and registry and push the feature branch.  If any gate fails, do not perform a
fourth pass or edit source: preserve the artifacts, report the exact failure in
the registry, and stop.  Never push `main` or begin primary cleanup.

The frontier README/TeX and the 57-page primary exposition remain fully frozen
during stage three.

**User scope override.**  The stage-three invocations finished before a later
explicit narrowing, but their generated frontier PDF was never copied,
staged, committed, or pushed.  It must remain sidecar-only and receives no
coordinator review, validation, or integration claim.  All further frontier
work and all primary claim/layout auditing stop in this task; another worker
owns any frontier continuation.  The frontier lease and stage-three token are
released.

**Primary compile-only result.**  The branch merged main `682222de1`
conflict-free at clean pushed tip `6397a0d6a`.  The unchanged primary source
has Git blob `e3a0df24e` and SHA-256
`F4EE348F21524C2EDB8880E16E50802CCC6A3A831D38C8426F23AF7607EA64F1`.
Exactly three fresh `pdflatex` passes used the authorized sidecar job name and
all exited 0.  The final output has 57 pages, with zero undefined
references/citations, rerun requests, changed-label warnings, fatal errors, or
LaTeX errors.  Its extracted text is byte-identical to the tracked canonical
PDF, so the worker correctly avoided timestamp-only canonical-PDF churn.  No
primary source/PDF or generated frontier PDF was staged.  This is compile
confirmation only, not a claim/layout audit.

After that scope close, merge tip `6397a0d6a` independently advanced `main`
and made the branch's frontier README, TeX, and registry source checkpoint
reachable.  It changed neither the frontier PDF nor any primary path.  Preserve
the forward history, but do not treat the resulting mismatched frontier
TeX/PDF pair as a validated final artifact: the user-designated successor owns
its disposition and any matching rebuild.

The exposition task is complete under the user's narrowed scope.  Its EVO
token and all document ownership are released.  Do not resume its frontier or
primary work; any successor frontier owner must be identified separately on
this board.

### `codex/fabius-theorem-refinements`

The task had successfully aborted its earlier conflicted merge, but later
merged successive main checkpoints; its tip `05ad144c7` became the first parent
of merge tip `1570b29b9`, which advanced `main`.  That incident is closed.  The
branch may sync and begin new ordinary, nonoverlapping work under the shared
protocol, but must not replay or re-extract the integrated tranche.  Exactly
seven public Lean names were the intended extraction,
all from `a95bd1913` in
`FabiusQBinomialTaylor.lean`: translated Thue--Morse polynomial coefficient,
zero, self-value, zero-iff, natural-degree, leading-coefficient, and degree
APIs.  The source blob now on `main` matches the independently extracted blob
at coordinator branch `a6fa59157` exactly; serialized focused and
`PaperFabiusAsymptotic` builds of that extraction both exited 0.

The pathwise audit accepts the other nine Lean/root/facade blobs: five contain
only accurate comments and four comment-only paper facades add only
`set_option autoImplicit false`; no declaration, proof, signature, import,
instance, or API changes.  Exact compilation found and fixes forward the sole
syntax defect in that prose tranche by placing the `partialSum_smul` doc comment
before its existing `@[simp]` attribute.  It also accepts the 14-page
non-elementarity TeX/PDF pair from semantic merge `1b2cd37dd`, the missing
audit code fence, and the two SHA-bound Claude registry updates.  The dead
coverage link and stale current-state wording in both Codex registries are
fixed forward in the coordinator acceptance commit.  The branch history and
content are retained; do not cherry-pick `a6fa59157`, whose source is already
present.

### Claude Fabius branches and any unlisted branch

The observed Claude asymptotic, documentation, theorem, and non-elementarity
tips are ancestors of the campaign base.  Their old leases are closed.  Any
continued work, and any branch not named above, may begin after it pushes an
exact-path/declaration claim in its own registry and verifies that the claim is
ordinary and nonoverlapping.  No coordinator acknowledgement is needed unless
a requested path is serialized, hot, frozen, single-owner, or already claimed.

## Collision and integration queue

No reviewed Lean workstream is waiting on a validation token.  The
four disjoint both-papers units, periodic bridges, all-index oddness, private
spline cleanup, reflected Laplace moments, and the shifted-prefix seven-name
tranche are integrated and validated as recorded above.  Continue to avoid
merging either moving feature history wholesale.  The generic Rvachev bridge
and Lambert-rate equivalence tranches are also integrated, repaired, compiled,
and released.  The all-degree complex branch theorem, its downstream all-real
continuation, and the disjoint coarse eighth-order reference-tail tranche are
integrated, compiled, and released.

The both-papers product-positivity consolidation, theorem-polish normalized
Laplace-reflection tranche, and shifted-prefix signed dyadic-reflection tranche
are also integrated and green.  The total binary-reduction, normalized-`L¹`,
and Unit-Laplace tilt-comparison tranches are now integrated, compiled, and
released as well.  The disjoint both-papers shifted-Fourier tranche is also
integrated, compiled, and released; it grants no document ownership.  The
subsequent two-file saddle continuous-polynomial deduplication is integrated,
compiled, and released under its explicitly narrowed two-name public surface.
The theorem-polish compact Lambert-W obstruction is integrated at `8d928a55f`
and its 3891-job focused build is green.  Its settled 59-page primary
TeX/PDF pair is integrated at `260d66fce`, with the narrow registry release at
`ff41c127a`; all document and TeX ownership is released.  The both-papers
central-binomial valuation tranche is likewise integrated at `430aaac90`,
green through its 2017-job focused and 3244-job paper-facade builds, and
released.  Its general Kummer carry-cocycle successor is integrated at
`598ad5850`, green through a second 2017-job focused and 3244-job paper-facade
pair, and released.  The effective-bounds all-order Lambert-polynomial
tranche is integrated at `5cc6970fd`, repaired at `128890b71`, green through
its 3249-job focused and 3253-job direct-consumer builds, and released.  The
subsequent both-papers denominator consolidation is integrated at `a7946a7a9`,
green through its 3419-job upstream and 3501-job downstream builds, and also
released.  The effective-bounds strict-moment source is integrated at
`63e7334ec`, and its all-real cumulant successor at `5100bc049`; their separate
3417-job and 2858-job focused builds plus the shared 3419-job downstream gate
are green, and both leases are released.

The effective-bounds binary constant-three sharpening is integrated at
`942fd6b68`, green through 2820-job focused and 3324-job direct-consumer
builds, and released.  The both-papers private-only deletion is integrated at
`611fb96ff`, green through independent 3244-job OriginalUniqueness and
2715-job LegendreSeriesConvergence builds, and released.  The complete staged
inverse stack is integrated through `6d5a6c09c`, green through the 2011-job
generic, 3931-job endpoint, and 3960-job paper-facade gates.  The theorem-polish
exact cluster-set source sequence is integrated through `508341204`, repaired
at `e332a58fd`, and green through its 3891-job Sharp gate plus fresh 3931/3960
downstream inverse/facade gates.  Every associated source path and build token
is released; neither tranche activates a document lease.

Theorem-polish source commit `665b6bce` is integrated as `c80f61c90`, repaired
without statement changes at `6b6757e90`, and accepted after its focused
3187-job build exited 0.  Its `ProbabilityLaplaceMoments.lean` lease is
released.

Frontier source checkpoint `6397a0d6a` is already on `main` without a matching
rebuilt PDF historically; accepted merge `192c423bb` now closes that mismatch
with the reviewed 188-page artifact.  The shifted-prefix and theorem-polish
document releases leave every canonical document path frozen.  Both TeX/PDF
lanes and both host Lean/Lake tokens are idle and unassigned except that the
coordinator retains codexbox Lean/Lake ownership.  Ordinary nonoverlapping
feature claims may continue under the shared protocol, but no worker may start
a Lean/Lake or document process until a later board grant.

## Build-token log

At 15:45 PDT the coordinator observed two concurrent jobs on `codexbox`:

- worktree `042c`: `lake build +FabiusFunction.FabiusFullAsymptoticExpansion`;
- worktree `/home/codex/src/Proofs`: `lake env lean /tmp/LowerLambertWPrototype.lean`.

Those jobs exited, but the same worktree later launched concurrent
`LowerLambertWPrototype` and `FabiusInversePowerBridgeAudit` jobs.  After they
exited, the coordinator started the sole immutable integration build at
`9e4dbec20`; a new unassigned `FabiusGammaZetaSignAudit` job then appeared.
The coordinator stopped only its own build (exit `130`) and makes no validation
claim from that interrupted attempt.

After the lane became quiet, the coordinator held the token and completed
these serialized immutable validations:

- at `9e4dbec20`: `+FabiusFunction.BromwichSaddle` and
  `+FabiusFunction.PaperFabiusAsymptotic`, both exit 0;
- at `4c6bbac41`: `+FabiusFunction.LowerLambertW`, exit 0;
- at `60458909a`: `+FabiusFunction.FabiusUniformSpline`,
  `+FabiusFunction.FabiusDiscreteLimitIntegration`,
  `+FabiusFunction.FabiusComputability`, and
  `+FabiusFunction.PaperFabiusAsymptotic`, all exit 0.
- at source-only extraction `a6fa59157`:
  `+FabiusFunction.FabiusQBinomialTaylor` (3320 jobs) and
  `+FabiusFunction.PaperFabiusAsymptotic` (3957 jobs), both exit 0.

At acceptance commit `f3719da05`, the first
`LAKE_JOBS=1 lake build +FabiusFunction` attempt reached 4007/4008 completed
jobs but exited 1 because `SaddleExpansionAlgebra.lean:358` placed a doc comment
after `@[simp]`; Lean expected the declaration immediately after the attribute.
All other jobs in that invocation passed.  The retry is assigned only after the
comment is moved before the attribute in a new immutable commit.

At syntax-fix commit `9887ea584`, the retry
`LAKE_JOBS=1 lake build +FabiusFunction` completed all 4008 jobs and exited 0.
This is exact-tree validation of every current Lean module and closes the
integration incident.

At natural-knot reconciliation `068fc1be5`, the coordinator held the codexbox
token and ran two separate `LAKE_JOBS=1` targets:

- `+FabiusFunction.GlobalExtension` completed 2765 jobs, exit 0;
- `+FabiusFunction.Paper06487` completed 3244 jobs, exit 0 and transitively
  covered `PaperStatements` plus `Paper06487Supplement`.

For the all-real Laplace tranche, `+FabiusFunction.NegativeLaplace` (2831
jobs) and `+FabiusFunction.LaplaceMoments` (2857 jobs) exited 0 at merge
`0d308188c`.  The first `+FabiusFunction.NegativeLaplaceDerivatives` attempt
then exited 1 on a definitional folding mismatch in the new `ContDiff` proof;
it supplied no validation evidence.  After the narrow elaboration repair at
`c4bc42f16`, that target completed 2858 jobs and exited 0.  At the same repaired
tree, `+FabiusFunction.NegativeLaplaceVertical` (3194 jobs),
`+FabiusFunction.LaplaceMomentBounds` (3417 jobs), and
`+FabiusFunction.PaperFabiusAsymptotic` (3957 jobs) all exited 0.  The two
upstream source blobs are unchanged by the repair.

At shifted-grid merge `ae16882d5`, the coordinator retained the codexbox token
and ran four separate targets: `+FabiusFunction.ThueMorseGenerating` (2085
jobs), `+FabiusFunction.ThueMorseApproximation` (3307 jobs),
`+FabiusFunction.ThueMorseExponential` (2086 jobs), and
`+FabiusFunction.PaperKFoldThueMorse` (3327 jobs).  All exited 0.

At exact both-papers integration merge `04d619814`, the coordinator ran ten
separate serialized targets: `+FabiusFunction.DyadicAnalytic` (2772 jobs),
`+FabiusFunction.GlobalExtension` (2765), `+FabiusFunction.GlobalDyadic`
(2785), `+FabiusFunction.OriginalPaperSupplement` (3210),
`+FabiusFunction.BoseFinitePartIntegral` (3268),
`+FabiusFunction.PeriodicMean` (3269),
`+FabiusFunction.PeriodicRegularity` (3295),
`+FabiusFunction.PeriodicSmooth` (3297), `+FabiusFunction.Paper05442` (3417),
and `+FabiusFunction.PaperFabiusAsymptotic` (3957).  All used `LAKE_JOBS=1`
and exited 0.

At finite-jet source checkpoint `62ab80d03`, the coordinator ran
`+FabiusFunction.ThueMorseGenerating` (2085 jobs),
`+FabiusFunction.ThueMorseApproximation` (3307),
`+FabiusFunction.ThueMorseExponential` (2086), and
`+FabiusFunction.PaperKFoldThueMorse` (3327) serially; all exited 0.  The
Approximation module reports only the two documented nonblocking compatibility
linters.

For the discrete-shift tranche, the first Toeplitz attempt at `de8707b44`
failed on proof elaboration and supplies no validation evidence.  After repair
`8e09c4d98`, `+FabiusFunction.FabiusDiscreteLimitToeplitz` (3320 jobs) and
`+FabiusFunction.FabiusDiscreteLimitIntegration` (3422 jobs) both exited 0
without warnings.

For the four later both-papers units, the coordinator retained the sole
codexbox token and ran each required target in a separate `LAKE_JOBS=1`
invocation on the exact cumulative coordinator tree:

- at `f975de00f`, `+FabiusFunction.AnalyticMoments` completed 2828 jobs,
  exit 0;
- at `f62058b96`, `+FabiusFunction.FourierProduct` completed 3190 jobs,
  exit 0;
- at `29729991e`, `+FabiusFunction.HalfQBinomial` completed 2020 jobs and
  `+FabiusFunction.FabiusQBinomialFormula` completed 3317 jobs, both exit 0;
- at `6f98e4804`, `+FabiusFunction.FabiusSharpAsymptotic` completed 3891 jobs
  and `+FabiusFunction.PaperFabiusAsymptotic` completed 3957 jobs, both exit 0.

Before the green AnalyticMoments invocation, the same command was issued once
from `Analysis/FabiusFunction/Lean`, which has no Lake configuration.  It
exited 1 immediately without launching Lean and supplies no evidence.  All
subsequent commands used the repository root.

For the periodic derivative bridges, the first
`+FabiusFunction.PeriodicSmooth` attempt at `af3132a31` exited 1 on the two
documented proof-elaboration defects and supplies no validation evidence.
After statement-preserving repair `8d269396a`, the same serialized target
completed 3297 jobs and exited 0 without warnings.

For all-index oddness, `+FabiusFunction.Paper06487Supplement` at
`6d15d9116` completed 3243 jobs and
`+FabiusFunction.Paper06487` completed 3244 jobs, both exit 0.  For the dead
private spline-helper cleanup, `+FabiusFunction.FabiusUniformSpline` at
`b16fc9a6d` completed 3415 jobs, exit 0.

For all-order reflected Laplace moments, the first
`+FabiusFunction.ProbabilityLaplaceMoments` attempt at `c80f61c90` exited 1
because bare `simp [neg_pow]` recursively reconsidered its generated
`(-1)^j` factor; it supplies no validation evidence.  After the
statement-preserving explicit-identity repair `6b6757e90`, the same serialized
target completed 3187 jobs in 18 seconds and exited 0 without warnings.

For the generic Rvachev bridge, the first
`+FabiusFunction.Differential` attempt at `12fda28c7` exited 1 because
unrestricted simplification unfolded `fabiusReal` before applying the generic
left-tail hypothesis at `rvachevUp F 1`; it supplies no validation evidence.
Repair `15563b7dd` states the two fold-endpoint zeros explicitly without
changing a theorem statement.  At that tree, separate serialized builds of
`+FabiusFunction.Differential` (2653 jobs) and `+FabiusFunction.Existence`
(2783 jobs) both exited 0 without warnings.

For reciprocal Lambert rates, the first
`+FabiusFunction.FabiusLambertRates` attempt at `5fbdf6139` exited 1 because
`simpa` did not eta-reduce Mathlib's pointwise inverse functions; it supplies
no validation evidence.  Repair `2a5be17f3` makes the definitional function
shape explicit, changing no public statement.  At that tree, separate
serialized builds of `+FabiusFunction.FabiusLambertRates` (3252 jobs) and
`+FabiusFunction.FabiusSharpAsymptoticTransfer` (3341 jobs) both exited 0
without warnings.

For the all-degree complex branch estimate, separate serialized builds at
`f6cb1efd8` of `+FabiusFunction.FabiusDiscreteLimitComplexShift` (1873 jobs)
and `+FabiusFunction.FabiusComplexShiftSpline` (3417 jobs) both exited 0
without warnings.

For the downstream all-real complex-spline continuation, a serialized build at
`19ee18206` of `+FabiusFunction.FabiusComplexShiftSpline` completed 3417 jobs
and exited 0 without warnings.

For the coarse eighth-order reference-tail tranche, separate serialized builds
at `f85409a18` of `+FabiusFunction.FabiusSaddleReferenceTail` (3432 jobs) and
`+FabiusFunction.GaussianPolynomialTail` (3436 jobs) both exited 0 without
warnings.  An earlier command issued from a directory without a Lake project
configuration exited before invoking Lean and supplies no validation evidence.

For the product-positivity consolidation, separate serialized builds at
`77e2f55d4` of `+FabiusFunction.ExactInversePower` (2013 jobs) and
`+FabiusFunction.PaperStatements` (3242 jobs) both exited 0 without warnings.

For normalized Laplace reflection, a serialized build at `853a09a80` of
`+FabiusFunction.ProbabilityLaplaceMoments` completed 3188 jobs and exited 0.
It reported one nonblocking `unnecessarySimpa` linter in the new reflection
proof and no other warning.

For signed dyadic-prefix reflection, separate serialized builds at
`f66ef224b` of `+FabiusFunction.ThueMorsePrefix` (2019 jobs) and
`+FabiusFunction.FabiusRawQBinomialFormula` (3319 jobs) both exited 0 without
warnings.

For total binary-reduction estimates, separate serialized builds at
`9f4b6be52` of `+FabiusFunction.FabiusBinaryReductionSeries` (2819 jobs) and
`+FabiusFunction.FabiusGlobalQBinomialSeries` (3323 jobs) both exited 0 without
warnings.

For the normalized-`L¹` transfer bounds, separate serialized builds at
`caed8800e` of `+FabiusFunction.QuantitativeSaddle` (2782 jobs) and
`+FabiusFunction.SaddleAllOrders` (2783 jobs) both exited 0 without warnings.

For the Unit-Laplace tilt comparison, separate serialized builds at
`7b892b41c` of `+FabiusFunction.UnitLaplaceMomentBounds` (3189 jobs) and
`+FabiusFunction.LaplaceMomentBounds` (3417 jobs) both exited 0.  Both reported
only the inherited nonblocking `unnecessarySimpa` linter in
`ProbabilityLaplaceMoments.lean`.  Two preliminary commands were issued from
nested directories without a Lake configuration; both exited before invoking
Lean and supply no validation evidence.

For shifted real-axis Fourier decay, separate serialized builds at
`49ddce559` of `+FabiusFunction.PoissonSummation` (3195 jobs) and
`+FabiusFunction.Paper05442` (3417 jobs) both exited 0 without warnings.

For saddle continuous-polynomial deduplication, separate serialized builds at
`9aca1aaf3` of `+FabiusFunction.FabiusSaddleExpansionCoefficients` (3306 jobs)
and `+FabiusFunction.FabiusSaddleReferenceWeight` (3517 jobs) both exited 0.
The latter replayed only the inherited nonblocking `unnecessarySimpa` linter
in `ProbabilityLaplaceMoments.lean`.

On EVO, exact shifted-prefix merge `4367a7f86` and tree `db635e6a073b`
preserved source commits `8021c555f` and `f7152d5fc`.  Separate sequential
`LAKE_JOBS=1` builds of `+FabiusFunction.FabiusQBinomialTaylor` (3320 jobs),
`+FabiusFunction.ThueMorseApproximation` (3307 jobs), and
`+FabiusFunction.PaperKFoldThueMorse` (3327 jobs) all exited 0.  The latter two
reported only the two intentionally retained unused-`hk` compatibility
linters.  No fourth target or overlapping process ran; the EVO token is
released.

On EVO, stage two at source tip `1ca2a09be` ran exactly three sequential
frontier `pdflatex` passes under the authorized fresh `_stage2` job name.  All
three exited 0 and produced 178, 186, and 186 pages.  The third pass was
reference/citation-stable and free of duplicate labels, horizontal overfull
boxes, rerun requests, changed labels, and fatal/LaTeX errors, but it contained
one 59.28255pt overfull `\\vbox` immediately before page 184.  The worker
stopped and preserved the rejected PDF/log without touching the canonical PDF.
This run fails the zero-overfull-box gate and grants no PDF validation; its
token is released pending a source-only repair checkpoint.

The exposition branch later completed the authorized three stage-three
frontier passes, but before any canonical copy, staging, evidence commit, or
push the user explicitly ended frontier work in that task.  The generated PDF
and log remain sidecars.  They are not reviewed or accepted here, and no
frontier validation or integration claim follows from them.

The subsequent compile-only primary check at source blob `e3a0df24e` ran three
fresh `pdflatex` passes, all exit 0.  Final output was 57 pages with no undefined
reference/citation, rerun, changed-label, fatal, or LaTeX-error diagnostic.
Extracted text matched the tracked canonical PDF byte-for-byte, so no PDF was
replaced or staged.  This closes only the requested compilation confirmation.

Before those green runs, one command launched from the wrong directory was a
no-op, and the first correctly rooted attempt exhausted the filesystem while
creating a fresh `.lake`; it exited 1 and supplied no validation evidence.
The coordinator removed only that generated failed cache, then copied an idle
worktree's dependency cache and reran at the immutable source tree.  During the
worker checkpoint, `/home/codex/src/Proofs` also launched an unassigned
`lake env lean` prototype check; it exited and is not treated as integration
evidence.

No validation process was running on codexbox when the original PDF grant was
published.  A lightweight sequential TeX/PDF lane is independent of the
one-process codexbox Lean/Lake token when the board assigns a document owner;
both codexbox lanes are currently idle, and the Lean/Lake token remains
coordinator-owned.  The coordinator used that token at exact integrated trees
for `+FabiusFunction.FabiusSharpAsymptotic` (3891 jobs, exit 0; inherited
`ProbabilityLaplaceMoments.lean` linter only), then
`+FabiusFunction.TwoAdic` (2017 jobs, exit 0) and
`+FabiusFunction.Paper06487` (3244 jobs, exit 0), with no overlap between
processes.  It later ran the repaired all-order Lambert gates
`+FabiusFunction.FabiusLambertAllOrderAlgebra` (3249 jobs) and
`+FabiusFunction.FabiusLambertFormalLog` (3253 jobs), then the denominator
consolidation gates `+FabiusFunction.NegativeLaplaceDerivativeBounds` (3419
jobs) and `+FabiusFunction.FabiusLambertDerivativeBounds` (3501 jobs), all
sequential and exit 0.  The sole diagnostics in the latter pair were the
inherited `ProbabilityLaplaceMoments.lean` linter.  The superseded initial
all-order Lambert build failed only at the five proof-normalization sites
repaired by `128890b71` and provides no theorem validation.  On the later
combined strict-moment/cumulant tree it ran, still serially,
`+FabiusFunction.LaplaceMomentBounds` (3417 jobs),
`+FabiusFunction.NegativeLaplaceDerivatives` (2858 jobs), and the shared
downstream `+FabiusFunction.NegativeLaplaceDerivativeBounds` (3419 jobs), all
exit 0 with only the inherited linter.  At exact general-cocycle integration
`598ad5850`, it then ran a second `+FabiusFunction.TwoAdic` gate (2017 jobs)
and `+FabiusFunction.Paper06487` gate (3244 jobs), both sequential, exit 0,
and warning-free.  Separately, theorem-polish used EVO's sole sequential
TeX/PDF stream for three `pdflatex` passes at document source `2546fe21b`;
they exited 0 with 57, 59, and 59 pages, and the settled final artifact passed
the static, font, text, and raster gates recorded above.  That document stream
is released.  EVO's Lean/Lake and TeX/PDF tokens are now idle and unassigned.

For the binary constant-three follow-up, a preliminary command from a nested
directory without a Lake configuration exited before Lean and supplies no
evidence.  From the repository root, separate serialized builds of
`+FabiusFunction.FabiusBinaryReductionSeries` (2820 jobs) and
`+FabiusFunction.FabiusGlobalQBinomialSeries` (3324 jobs) both exited 0 without
warnings.  For the private-only cleanup, separate serialized builds of
`+FabiusFunction.OriginalUniqueness` (3244 jobs) and
`+FabiusFunction.LegendreSeriesConvergence` (2715 jobs) both exited 0 without
warnings.

For generic quadratic inversion, the first correctly rooted build exposed
only eleven function/Pi/algebra normal-form errors; a repair retry exposed two
remaining proof-shape errors.  Neither supplies validation evidence.  After
statement-preserving repair `863954b6a`,
`+FabiusFunction.QuadraticAsymptoticInversion` completed 2011 jobs, exit 0,
without warnings.  Endpoint source then had one parse-only missing-scope
failure followed by three, then one, elaboration-normal-form failures; none
supplies evidence.  Repair `6d5a6c09c` made no statement change, after which
`+FabiusFunction.FabiusInverseAsymptotic` completed 3931 jobs and
`+FabiusFunction.PaperFabiusAsymptotic` completed 3960 jobs, both exit 0 with
only the inherited `ProbabilityLaplaceMoments.lean` linter.

For the exact cluster-set tranche, one command issued from
`Analysis/FabiusFunction` found no Lake configuration, launched no Lean, and
supplies no evidence.  The first repository-root Sharp build compiled the new
Wikipedia main and obstruction modules but exited 1 at the final module on
the documented type-inference/function-normal-form sites.  After proof-only
repair `e332a58fd`, `+FabiusFunction.FabiusSharpAsymptotic` completed 3891
jobs and exited 0.  Fresh cumulative-tree builds of
`+FabiusFunction.FabiusInverseAsymptotic` (3931 jobs) and
`+FabiusFunction.PaperFabiusAsymptotic` (3960 jobs) then both exited 0.  Those
three final runs reported only the inherited linter.  Every invocation in this
checkpoint was serialized; the codexbox and EVO tokens are released.

Other branches may edit, checkpoint, and push ordinary claimed work under the
open protocol, but may not run Lean/Lake or a document tool stream until this
board assigns the applicable lane.

## Worktree maintenance log

With the user's explicit authorization, the coordinator removed two codexbox
worktrees whose last activity was more than one week old and whose processes
were not live:

- clean worktree `97db`, branch `codex/port-foundation-theorems`; committed
  remote tip `8b273f16f` remains available;
- dirty worktree `44ac`, branch `codex/quintic-radical-completeness`; committed
  remote tip `c29cbb447` remains available, but its 12 modified tracked files
  and 3392 untracked files were uncommitted and are unrecoverable.

This recovered enough disk space for the isolated coordinator cache.  Future
week-idle pruning follows the preservation rule above: push even a clearly
labelled WIP checkpoint if the work must survive.

## Worker reply template

Commit this block to your own registry file and push the feature branch:

```text
SYNC Fabius
branch / worktree / machine:
fetched main SHA:
HEAD and dirty paths:
writing (exact paths):
expected declarations or document claims:
completed commits:
validated (exact command, SHA/state, exit code):
not yet validated:
requested integration or lease:
conflicts / dependencies:
next bounded step:
```
