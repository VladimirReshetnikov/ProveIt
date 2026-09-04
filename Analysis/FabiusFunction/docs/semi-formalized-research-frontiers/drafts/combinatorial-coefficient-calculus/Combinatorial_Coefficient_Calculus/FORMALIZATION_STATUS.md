# Formalization campaign status

This is the handoff for the campaign begun on 2026-09-04. The **Lean
formalization register** in `Combinatorial_Coefficient_Calculus.tex` is the
single claim inventory; this file records validation, provenance, and remaining
work. Mathematical statements and proofs belong in the TeX/PDF pair. A register
classification records a claimed correspondence, not a fresh compilation receipt.

## Current checkpoint

The merged manuscript contains 209 theorem-like entries: **64 `Lean`,
36 `partial`, and 109 `none`** after the current claim audit. The audit corrected
two overclaims for the Abel and Fréchet statements and confirmed the
second-kind Stirling counting interpretation through
`BellSetPartitions.card_setPartitions`. This is a source-correspondence result
using the upstream receipt, not a fresh compilation of that module in this
campaign. Compilation of an algebraic source module does not establish every
hypothesis or analytic assertion in a broader human-readable theorem.

The six campaign leaves contain **25 new public theorems: five compiled and
20 pending compilation**. The thirteen generalized existing Lagrange helpers
are a separate compiled result, not additional new declarations.

| Campaign leaf | New public theorems | Current validation |
| --- | ---: | --- |
| `NewtonReciprocal` | 5 | Focused compilation passed with exit zero and no diagnostics. |
| `StirlingSymmetricFunctions` | 4 | Independent source/API review completed; compilation pending. The two second-kind evaluation formulas were deduplicated into upstream `StirlingCompleteHomogeneous`. |
| `LagrangeInversionUniqueness` | 6 | Source reviewed. The first compilation attempt hit the elaboration heartbeat limit while inferring a unit witness. Explicit proof data now replace that inference; the corrected source awaits retry. |
| `StirlingSecondReverseRowIdentity` | 2 | Independent source/API review completed, including the latest factorial-proof simplification; compilation pending. |
| `ExponentialRiordanInverse` | 4 | Independent review in progress; compilation pending. |
| `LagrangeExistence` | 4 | Independent review in progress; compilation pending. |

`LagrangeInversion.lean` itself passed direct compilation after its section
assumptions were corrected: thirteen existing helper/existence theorems and the
solution definition now work over arbitrary commutative rings. The coefficient
arguments that divide by positive integers retain their rational-algebra
assumptions. No aggregate corpus build is claimed.

The current campaign rebuilds the canonical TeX/PDF pair. **Rendering is pending
at this checkpoint**; page count and final source/render parity will be recorded
after the build owner completes and checks the render. Statements inherited
from other source-only sessions that PDF rebuilding was skipped at their user's
request describe those historical sessions only; they are not an instruction
or waiver for this campaign. PDF rendering and Lean compilation remain separate
validation results.

## Compilation and source-review receipts

- On 2026-09-04, `NewtonReciprocal.lean` passed the focused command below with
  exit zero. Its initial source preflight had missed a coefficient-API argument
  order error; the build owner corrected it with an explicitly typed function
  before the successful compilation.

  ```text
  lake env lean -o .lake/build/lib/lean/FabiusFunction/NewtonReciprocal.olean Analysis/FabiusFunction/Lean/FabiusFunction/NewtonReciprocal.lean
  ```

- Commit `baefb1b5b` records the rational-algebra assumption repair in
  `LagrangeInversion.lean`. Its direct compilation returned exit zero with no
  diagnostics. Immediate dependency source and imported-artifact fingerprints
  were checked before that build.
- The first `LagrangeInversionUniqueness` attempt reached the default elaboration
  heartbeat limit while matching an unspecified unit witness in the constructed
  inverse. The correction supplies the witness and outer series explicitly.
  No heartbeat limit was raised and no mathematical statement was weakened;
  the revised proof remains uncompiled.
- The `StirlingSecondReverseRowIdentity` preflight caught rational subtraction
  in the logarithmic-tail coefficient being mistaken for natural subtraction.
  An explicit rational normalization corrected that mismatch. Its later
  factorial proof reuses Mathlib's casted binomial-coefficient formula and
  direct reciprocal cancellation. Independent review found no further concrete
  blocker. Exact integer, rational, and finite-modulus checks are supporting
  arithmetic checks, not kernel validation.
- Commit `720646f3b` introduces `ExponentialRiordanInverse` and
  `LagrangeExistence`, with four new public theorems each. Their construction
  proofs and manuscript counterparts are present; review and compilation
  status are recorded in the current table above.

The source-only conclusions for the pending leaves remain limited. The
Stirling review checked the Vieta subset cardinality, semiring homogeneity,
empty families, and repeated values in positive characteristic. The Lagrange
review checked substitution associativity, inverse identities, coefficient
integration by parts, and unit cancellation. A source review can miss
elaboration behavior, as the concrete compiler and preflight corrections above
demonstrate.

## Historical checkpoint receipts

These figures belong to the named snapshots, not to the current 209-entry
manuscript, and do not establish a rebuild of the merged tree.

| Snapshot or receipt | Recorded evidence |
| --- | --- |
| Initial 2026-09-04 audit | 201 theorem-like environments: 150 theorems, 26 corollaries, 12 propositions, six lemmas, seven algorithms; register totals 56 `Lean`, 33 `partial`, 112 `none`; no conjecture environments. |
| First integration through `c668cb96362acbae8b89950102b8ea361102a73f` | Structural validator passed with 206 theorem-like items and adjacent proofs, 27 dispositions, and six immutable source-inventory rows. Its register reported 60 `Lean`, 35 `partial`, 111 `none`. The duplicate-crosswalk validator's eight regression tests passed. |
| Nörlund synchronization through `2ccc7f787becde416b234d40093876eac9f9c35e`, source checkpoint `16975fdfd` | The reported register had 207 entries, classified 60 `Lean`, 35 `partial`, 112 `none`. The new Nörlund and Bernoulli formal-logarithm extensions had source/API review, not compilation. |
| Main merge `28de4e51c` | Retained the nine compiled grid/CRT certificate theorems from `5a685136b`. Its reported register had 207 rows, classified 62 `Lean`, 35 `partial`, 110 `none`; its corpus census reported 985 modules and 12,199 public declarations. |
| Earlier source integration audit | 3,439 distinct cited names resolved with no duplicate declaration names. Missing facade imports for `AssociahedronFaceNumbers` and `PochhammerFalling` were restored. Generator syntax and mapping checks passed. These are structural checks, not a fresh aggregate Lean build. |

The first integration's pinned upstream merge sequence was:

```text
8159026c5310b24acb4d330a23836a473d7adaff
3f74ee23e479399595c91b5fb030c7fbceb23f1a
c5a82b88c40ad493d394056c8dd42ef6d3d306ac
063ef3e1b1c0403bd6c71d1c9aa265825504339c
8b6dbd52428744a8496c762fcdeb2cfebc0ba7cc
c668cb96362acbae8b89950102b8ea361102a73f
```

The obsolete live checksum ledger was retired during that integration. Source
recovery uses the immutable inventory and Git objects, not replacement ledgers.

## Claim boundaries retained from the audit

Paths below are relative to `Analysis/FabiusFunction/Lean/FabiusFunction` unless
explicitly identified as Mathlib. The table explains scope boundaries; it does
not duplicate the canonical register's status classifications.

| Canonical claim | Inspected source | Boundary to preserve |
| --- | --- | --- |
| `thm:merged-binomial-inversion` | `BinomialInversionEGF.lean` | Both formal generating-function directions are present over a commutative rational algebra; the old blanket denial was stale. |
| `thm:merged-moment-cumulant` | `CumulantBellFormula.lean` | Formal logarithm and closed Bell-polynomial formulas require normalization. They do not supply the separate weighted set-partition interpretation. |
| `thm:merged-catalan-first-return` | `SquareRootSeries.lean` | Formal square-root existence and uniqueness do not establish analytic branches or convergence. |
| `thm:merged-riordan` | `ExponentialRiordan.lean` and pending `ExponentialRiordanInverse.lean` | The existing inverse law assumes inverse data and proves one product. The new leaf constructs those data and addresses both products; its compilation is still required. |
| `thm:lagrange-burmann` | `LagrangeInversion.lean` and pending Lagrange leaves | The existing coefficient construction uses a supplied inverse of the weight. The new uniqueness, alternative-coefficient, and arbitrary-weight existence assertions have their own validation obligations. |
| `thm:second-recurrence` | Mathlib `Combinatorics/Enumerative/Stirling.lean` and `BellSetPartitions.lean` | `BellSetPartitions.card_setPartitions` supplies the counting bridge. The canonical successor-index recurrence states its zero boundaries explicitly. This campaign verified the source correspondence; no fresh compilation of the counting module is claimed. |

## Editorial work and remaining obligations

The campaign has consolidated contradictory or repetitive crosswalks, corrected
coefficient-ring and boundary assumptions, and repaired the Laplace endpoint
proof. Final source/render checks must cover the merged manuscript. The
substantive remaining work is:

1. **Pending kernel validation.** Compile the twenty pending new theorems and
   their missing or stale prerequisites serially. Retry the corrected Lagrange
   uniqueness proof before promoting its register entries. Complete independent
   reviews of the new Riordan and arbitrary-weight Lagrange leaves.
2. **Laplace endpoint formalization.** The repaired `thm:laplace-bell` states
   explicit analytic endpoint assumptions and complete remainder estimates.
   Its weighted coefficient identity, transformed Taylor remainder, and tail
   estimate still need Lean counterparts. A repaired human proof is not a
   completed formalization.
3. **Combinatorial semantics.** Retain the established second-kind Stirling
   set-partition cardinality bridge. Build the remaining per-profile weighted
   enumerators and surjection, cycle, and descent interpretations, sharing
   finite-set decomposition infrastructure where possible.
4. **Darboux analysis.** Preserve the exceptional polynomial cases and global
   remainder hypotheses. Formalize the gamma-ratio estimates, Cauchy bounds,
   convolution argument, and boundary integration by parts before upgrading
   the corresponding register entries.
5. **Analytic and formal calculus boundaries.** Formal composition and formal
   Leibniz lemmas require explicit bridges before they establish analytic
   Faà di Bruno, multinomial product, or inverse-derivative claims. Match every
   Abel and Fréchet assertion to the exact hypotheses of its cited declaration.
6. **Other pending upstream surfaces.** The Nörlund and Bernoulli formal-logarithm
   extensions retain their separate compilation obligations. General-order
   finite differences, multiplicity-vector interpretations, and analytic
   convergence must be tracked individually.
7. **Two-way exposition coverage.** Stable identifiers and the existing register
   must eventually cover mathematical prose, examples, algorithms, and public
   Lean support lemmas as well as theorem environments. Environment counts
   alone do not measure the user's requested two-way correspondence.

Structural validation, exact finite checks, source review, PDF parity, focused
Lean compilation, aggregate builds, and remote publication are distinct
receipts. None should be inferred from another.
