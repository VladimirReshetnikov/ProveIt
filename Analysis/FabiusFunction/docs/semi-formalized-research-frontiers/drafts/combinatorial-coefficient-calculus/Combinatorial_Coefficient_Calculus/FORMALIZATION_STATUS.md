# Formalization campaign status

This is the handoff for the campaign begun on 2026-09-04. The **Lean
formalization register** in `Combinatorial_Coefficient_Calculus.tex` is the
single claim inventory; this file records validation, provenance, and remaining
work. Mathematical statements and proofs belong in the TeX/PDF pair. A register
classification records a claimed correspondence, not a fresh compilation receipt.

## Current checkpoint

The merged manuscript contains 210 theorem-like entries: **77 `Lean`,
49 `partial`, and 84 `none`** after the current claim audit. The audit corrected
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
The finite-difference and Bell-multiplicity source checkpoint incorporates
main through `5fddefb43b6f4009df826b68aedbdb1c6112e0d0`. It adds seven public
theorems: three generic formulas in `BellCompletePartitions`, two
arbitrary-scalar difference laws and two multiplicity specializations in
`NorlundGeneralized`. Independent source/API review checked the factorial
normalizations, unrestricted zeroth Bell input, zero-ring scope, degree zero,
and negative orders. No Lean process was started while external Lean/Lake
jobs occupied the host; these declarations are not compiler-verified yet.
The generic human Bell proof is now shared by the Nörlund section.
At this checkpoint the generated register has 208 rows, classified as
62 `Lean`, 35 `partial`, and 111 `none`. The two added upstream `Lean`
classifications are inherited certificate work, not promotions from this
source review. Fourteen validator regression tests and the canonical
structural/provenance check pass. The manifest and package README now refer
to the canonical register instead of maintaining competing current totals.

The publication merge then incorporates pinned main
`ff76c57fa563102804b64c8c8abab90f47b09baf`. Its `BellSetPartitions`
module supplies the weighted labelled-set interpretation for both partial
and complete Bell polynomials, and the second-kind Stirling block count.
That module's focused compilation is recorded in upstream commit
`dd554e5a8`; this work performed an independent statement/hypothesis review,
not a fresh compiler replay. Its source changes the previously open
labelled-partition boundary but does not supply the prescribed-type count.
The merged register has 208 rows: 63 `Lean`, 35 `partial`, and 110 `none`.
The new local Bell multiplicity and arbitrary-order Nörlund statements
remain pending compilation.

The final synchronization at main `da90f69d1` recorded an upstream register of
208 rows: 64 `Lean`, 35 `partial`, and 109 `none`. At that historical snapshot
the Abel row was left `none` because source review is not compilation, and the
coordinate-free composition row was described through Mathlib's
`iteratedFDeriv_comp` and `FormalMultilinearSeries.taylorComp`. The current
branch re-audited both correspondences: Abel remains `partial` because its
universal polynomial transfer is still open, and the Fréchet statement remains
`partial` until the ordered-partition bridge is verified against the exact local
hypotheses. Neither historical description is a fresh local compiler run.

`NewtonReciprocal.lean` passed focused compilation on 2026-09-04 using
`lake env lean -o .lake/build/lib/lean/FabiusFunction/NewtonReciprocal.olean
Analysis/FabiusFunction/Lean/FabiusFunction/NewtonReciprocal.lean` (exit zero).
Its five public theorems are compiler-checked. The other twelve new public
theorems in the three Stirling/Lagrange leaves remain source-reviewed and await
compilation, including any missing prerequisites. No aggregate build is claimed.
At the upstream synchronization checkpoint the cited-name and duplicate-name
structural audits passed:
3,439 distinct cited names resolved and there were no duplicate declaration
names. The incoming alternate reverse-row declaration is now named
`Fabius.second_reverse_row_commRing_of_le`, avoiding a collision with the
compiled theorem while its own validation remains pending. The facade audit found two missing upstream imports,
`AssociahedronFaceNumbers` and `PochhammerFalling`; both were restored. These
structural checks are not a fresh aggregate Lean build. The reviewed new modules
contain no `sorry`, `admit`, `axiom`, or `opaque` declarations; import integration
for the alternate reverse-row source remains part of its pending validation. The register-generator mappings
preserve the pending and compiled distinctions; a dry run on a temporary source
copy reproduces the canonical register and its 207-row totals.

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

## New source preflight

`StirlingSymmetricFunctions.lean` was independently reviewed against the actual
imported APIs. Its four public theorems identify first-kind Stirling numbers
with elementary symmetric evaluations and state the common-scaling laws for
both Stirling triangles over every commutative semiring. The two second-kind
evaluation formulas were deduplicated into the compiled upstream
`StirlingCompleteHomogeneous` API. The review checked the empty-family cases, the natural
subtraction guard, the second-kind adjoining-variable recurrence, the precise
Vieta subset cardinality, and the multiset formulation that preserves repeated
values in positive characteristic. No concrete source or API blocker was found.
This is a preflight result, not a compiler result; the build owner records actual
compilation separately.

`NewtonReciprocal.lean` received a separate source/API review covering the scalar
initialization, exact squared-residual identity, divisibility witness, coefficient
precision, and preservation of that precision under actual polynomial truncation.
All five theorem statements are valid over an arbitrary commutative ring. The
preflight missed a concrete API error that the compiler caught:
`Polynomial.coeff` takes the polynomial before its index, unlike
`PowerSeries.coeff`. The build owner replaced the erroneous partial application
with an explicitly typed function from polynomials to their coefficient of the
chosen degree. The corrected file then passed the focused compiler invocation
recorded above with exit zero and no diagnostics.

`LagrangeInversionUniqueness.lean` was checked against the substitution-associativity,
compositional-inverse, derivative, and unit APIs. Its uniqueness argument and
Jacobian coefficient calculation are mathematically coherent. Source review
cannot confirm the elaborated typeclass signatures of imported declarations;
the compiler must in particular verify that their unused rational-algebra
instances are omitted as expected for the new commutative-ring uniqueness
statements. These six new theorems address the original uniqueness and alternative
coefficient obligations recorded in the inspected `LagrangeInversion.lean` row.

`StirlingSecondReverseRowIdentity.lean` was independently checked against the
existing Stirling-transform and logarithmic-tail APIs. Its two public theorems
state the complete rational transform and the finite reverse-row identity over
every commutative ring. The review checked the factorial kernel, coefficient
normalization, discarded zero prefix, finite-sum reindexing, binomial symmetry,
and transfer through the integers. It caught a mismatch between rational
subtraction in the logarithmic-tail denominator and natural subtraction in the
kernel helper; the author added an explicit rational normalization. The revised
source has no further concrete blocker identified, but awaits compilation.

## Substantive remaining obligations

1. **Laplace endpoint formalization.** The repaired `thm:laplace-bell` now assumes
   positive real exponents, analytic local factors, an integrable amplitude, a
   finite interval, and a strict endpoint minimum. Formalize its weighted
   Lagrange coefficient identity, the transformed Taylor remainder, and the
   exponentially small tail. The human proof is repaired; the Lean obligation
   remains. A broader asymptotic-germ theorem is a separate possible extension.
2. **Riordan inversion.** Construct the formal compositional and multiplicative
   inverses from the stated unit hypotheses; prove both array products and record
   their exact declarations. Until then distinguish the conditional inverse law
   from the full inverse construction in the register.
3. **Combinatorial semantics.** Reuse the incoming `BellSetPartitions`
   weighted-set decomposition and Stirling block-count bridge. Remaining
   obligations include prescribed block-size type counts, the literal partial
   Bell monomial formula, cycles, and descents. Algebraic recurrences alone
   cannot certify a counting interpretation; do not duplicate the completed
   weighted Bell bridge while extending it.
4. **Darboux analysis.** The corrected analytic-multiplier theorem explicitly
   handles polynomial exceptional exponents; the finite-smoothness subtraction
   theorem assumes a global decomposition and gives an explicit periodic boundary
   criterion. Source review found those two repairs mathematically coherent.
   Their gamma-ratio estimates, Cauchy bounds, convolution estimate, and boundary
   integration by parts still need actual Lean statements and proofs. No existing
   Darboux register row should be promoted merely because the human proof was
   repaired.
5. **Analytic and formal differential calculus.** The canonical ordered
   iterated-Fréchet-derivative composition formula is now explicitly mapped to
   Mathlib. Its partial-Bell tensor regrouping, the general multinomial product
   rule, and analytic inverse-derivative claims still require separate bridges;
   formal power-series identities alone do not discharge them.
6. **Two-way exposition coverage.** Give every presently unlabelled theorem-like
   environment a stable claim identifier. Extend the existing register to cover
   mathematical prose and examples, and identify which public Lean support
   lemmas belong in the exposition. Do not duplicate the canonical register in a
   second independently maintained inventory.

The next efficient milestones are small reusable formal-series results and
precise upgrades of currently partial rows. The much larger analytic and
combinatorial interpretation layers remain part of the open campaign; the
initial status totals must not be presented as an audit that all `Lean` rows have
already been recompiled or that all human claims have been checked.
