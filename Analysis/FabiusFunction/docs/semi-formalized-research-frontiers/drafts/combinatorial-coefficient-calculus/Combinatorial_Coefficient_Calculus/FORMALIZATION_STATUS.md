# Formalization campaign status

This is the handoff for the campaign begun on 2026-09-04. The **Lean
formalization register** in `Combinatorial_Coefficient_Calculus.tex` is the
single claim inventory; this file records validation, provenance, and remaining
work. Mathematical statements and proofs belong in the TeX/PDF pair. A register
classification records a claimed correspondence, not a fresh compilation receipt.

## Current checkpoint

The merge of main at `da90f69d1` retains the nine compiled grid/CRT certificate
theorems from `5a685136b`. Its regenerated register has 207 rows: 65 `Lean`,
35 `partial`, and 107 `none`; the historical corpus census was 1003 modules and
12,485 public
declarations. These pinned checkpoint counts and pending-build receipts describe
historical source states, not a rebuild of the current merged tree.

The merged manuscript contains 210 theorem-like entries: **77 `Lean`,
53 `partial`, and 80 `none`** after the current claim audit. The audit corrected
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

The canonical PDF is intentionally not rebuilt in this merge, at the user's
request. The retained PDF is a historical artifact whose byte identity is
preserved; the current source/PDF pair has no render-parity claim until a future
build is authorized.

The upstream synchronization receipts also record the earlier integration through
`c668cb96362acbae8b89950102b8ea361102a73f`, with structural validation and
crosswalk regression checks passing, followed by the Nörlund and Bernoulli
formal-logarithm extensions. The named receipts distinguish source review from
compiler validation and report the inherited 208-page PDF as historical. Those
historical figures are retained for provenance and do not replace the current
register or imply an aggregate build.

`NewtonReciprocal.lean` passed focused compilation on 2026-09-04 using
`lake env lean -o .lake/build/lib/lean/FabiusFunction/NewtonReciprocal.olean
Analysis/FabiusFunction/Lean/FabiusFunction/NewtonReciprocal.lean` (exit zero).
Its five public theorems are compiler-checked. At that checkpoint the other twelve
new public theorems in the three Stirling/Lagrange leaves awaited compilation.
The two reverse-row identity declarations have since passed the focused check
above; no aggregate build is claimed.
At the upstream synchronization checkpoint the cited-name and duplicate-name
structural audits passed:
3,439 distinct cited names resolved and there were no duplicate declaration
names. The generic `Fabius.second_reverse_row_commRing` has since passed focused
compilation. The facade audit found two missing upstream imports,
`AssociahedronFaceNumbers` and `PochhammerFalling`; both were restored. These
structural checks are not a fresh aggregate Lean build. The reviewed new modules
contain no `sorry`, `admit`, `axiom`, or `opaque` declarations. Both reverse-row
modules now pass focused compilation on their merged sources. The register-generator mappings
preserve the pending and compiled distinctions; a dry run on a temporary source
copy reproduces the canonical register and its current 210-row totals
(77 `Lean`, 53 `partial`, 80 `none`).

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

These figures belong to the named snapshots, not to the current 210-entry
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
| `thm:merged-binomial-inversion` | `BinomialInversionEGF.lean`: `Fabius.egfA_eq_exp_mul_iff`, `Fabius.egfA_eq_altSeries_mul_iff`, `Fabius.egfA_eq_exp_mul_iff_egfA_eq_altSeries_mul` | Both formal generating-function directions are present over a commutative rational algebra. The old adjacent statement that this part is unformalized was stale. |
| `thm:merged-moment-cumulant` | `CumulantBellFormula.lean`: `Fabius.logOf_egfA`, `Fabius.cumulant_eq_cumulantSum` | The formal logarithm and closed partial-Bell expression are present, assuming the moment sequence starts with one. This does not identify these recurrence-defined polynomials with sums over actual set partitions. |
| `thm:merged-catalan-first-return` | `SquareRootSeries.lean`: `Fabius.sq_sqrtOf`, `Fabius.sqrt_unique`, `Fabius.sqrtOf_one_sub_four_X` | The square-root identity is present as a formal series identity with constant term one over a commutative rational algebra. Analytic branch and convergence statements remain separate obligations. |
| `thm:merged-riordan` | `ExponentialRiordan.lean` and `ExponentialRiordanInverse.lean`: `Fabius.expRiordan_action`, `Fabius.expRiordan_mul`, `Fabius.expRiordan_mul_inverse`, `Fabius.riordanInverseWeight`, `Fabius.expRiordan_mul_constructedInverse`, `Fabius.expRiordan_constructedInverse_mul` | Action and multiplication are explicit. The inverse theorem is conditional; the constructed inverse leaf and its two-sided statement retain a separate compiler-validation receipt. |
| `thm:lagrange-burmann` | `LagrangeInversion.lean` and `LagrangeInversionUniqueness.lean`: `Fabius.Lagrange.solution`, `Fabius.Lagrange.solution_eq`, `Fabius.Lagrange.coeff_solution_subst_derivative`, `Fabius.Lagrange.coeff_solution`, `Fabius.Lagrange.eq_solution_of_eq_X_mul_subst`, `Fabius.Lagrange.existsUnique_solution`, `Fabius.Lagrange.existsUnique_of_isUnit_constantCoeff`, `Fabius.Lagrange.coeff_jacobian_mul`, `Fabius.Lagrange.coeff_subst_alt`, `Fabius.Lagrange.coeff_solution_subst_alt` | The construction, uniqueness, Jacobian identity, and alternative coefficient assertions have source/API receipts; the current campaign keeps their exact compiler obligations separate. Construction and uniqueness work over a commutative ring when the weight constant coefficient is a unit; coefficient formulas use a commutative rational algebra and `1\le n`. Formal power-series algebra is covered; analytic convergence and residue language are not asserted. |
| `thm:second-recurrence` | Mathlib `Combinatorics/Enumerative/Stirling.lean` and `BellSetPartitions.lean` | `BellSetPartitions.card_setPartitions` supplies the counting bridge, while Mathlib supplies the recursive successor-index array and its zero boundaries. This campaign has not freshly compiled the counting module. |

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
source has no further concrete blocker identified and now passes direct
sequential Lean elaboration.

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
