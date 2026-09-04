# Formalization campaign status

This is a source-review handoff for the campaign begun on 2026-09-04. The
canonical claim register is the **Lean formalization register** section of
`Combinatorial_Coefficient_Calculus.tex`; this file does not reproduce its rows.
Mathematical statements and proofs belong in the TeX/PDF pair. The register's
status words are recorded correspondence claims, not a fresh compilation receipt.

## Latest publication checkpoint (2026-09-04)

Main `17156aa2a` is integrated with all text and semantic name conflicts resolved.
The synchronized PDF has 213 A4 pages, with three serial strict passes, generated
index, and six focused page checks. Its final log has no undefined references,
overfull boxes, or rerun requests; Libertinus is present and no Type 3 fonts occur.

The source has 11,244 lines, 552,510 UTF-8 bytes, 209 adjacent proofs, 712 labels,
and 954 references. The regenerated register contains 64 `Lean`, 35 `partial`,
and 110 `none` rows. The structural/provenance validator and all 14 regression
tests pass; all 3,472 cited Fabius names resolve. The facade has 837 unique
imports and no missing source targets among 987 modules. An incoming import of
the absent `InverseDerivativeRecursion` module was removed. Pending proof
extensions remain pending: these source and render checks do not replay Lean.

## Preceding merge and validation checkpoint (2026-09-04)

At the checkpoint integrating main `095be8f0b`, the manuscript had 209 theorem-like
items and 209 adjacent proofs, 712 labels, 951 references, 27 disposition rows,
and six original-source inventory rows. Its 209-row register recorded 61 `Lean`,
35 `partial`, and 113 `none`; inherited compiler receipts are not fresh replay.
The source measured 11,155 lines and 546,097 UTF-8 bytes.

That synchronized PDF has 211 A4 pages. Three serial strict pdfLaTeX passes and
index generation succeeded; Libertinus text was present, with no Type 3 fonts,
undefined references, overfull boxes, or rerun requests. Six focused pages
covering the latest Nörlund additions, register, and index were visually checked;
the preceding merge's Laplace, Lagrange, symmetric-function, and Newton additions
were reviewed separately. No whole-volume visual or mathematical audit is claimed.

The canonical structural/provenance validator and all eight crosswalk regression
tests passed. All 3,458 cited Fabius names resolved in the source audit. The exact
finite Stirling/Bell regressions passed. The facade reached all 984 source modules;
duplicate imports and the duplicate public reverse-row declaration were removed.
These are source/finite/render checks, not Lean compilation. The merged proof
extensions and new wrappers remain pending while other worktrees use the build slot.

## Incoming grid and CRT certificate checkpoint

The current integration of pinned main `17156aa2a` retains the nine grid/CRT
certificate theorems from `5a685136b`. That commit records warning-free focused
builds and the standard three axioms for all nine declarations. Both
`GridEvaluationCertificate` and `IntegerCRTCertificate` have identical source
blobs at that receipt and at the incoming pin. Their Lean classifications are
therefore inherited receipts, not fresh compilation of this merged tree.
The incoming `28de4e51c` checkpoint recorded 207 register rows: 62 `Lean`,
35 `partial`, and 110 `none`, with a census of 985 modules and 12,199 public
declarations. Those counts and the preceding 211-page render describe their
historical source states. Fresh merged-source metrics, structural validation,
and render verification remain to be recorded by the publication owner.

## Inventory and evidence boundary

The initial source snapshot contained 201 theorem-like environments: 150 theorems,
26 corollaries, 12 propositions, 6 lemmas, and 7 algorithms. Its register had 201
rows, classified as 56 `Lean`, 33 `partial`, and 112 `none`. There are no conjecture
environments. These are environment counts, not counts of independently proved
assertions: several environments contain multiple identities, while definitions,
examples, prose, complexity claims, and numerical tables also contain mathematics.
The user's eventual two-way correspondence requirement therefore exceeds this
register's current scope.

The audit read the package policies, the canonical source, the declaration bodies
listed below, and selected relevant Mathlib definitions. It did not run Lean or
Lake, rebuild the PDF, or verify the full set of 201 correspondences. A successful
structural validator establishes neither mathematical correctness nor compilation.
Every additional formalization milestone needs its own precise validation record.

The first integration milestone merged pinned upstream
`8159026c5310b24acb4d330a23836a473d7adaff`, then
`3f74ee23e479399595c91b5fb030c7fbceb23f1a`, and
`c5a82b88c40ad493d394056c8dd42ef6d3d306ac`, followed by
`063ef3e1b1c0403bd6c71d1c9aa265825504339c` and
`8b6dbd52428744a8496c762fcdeb2cfebc0ba7cc` and
`c668cb96362acbae8b89950102b8ea361102a73f`. Its source validator passed with
206 theorem-like items and adjacent proofs, 27 dispositions, and six immutable
source-inventory rows. The obsolete live checksum ledger was retired as upstream
intended. That checkpoint's register had 60 `Lean`, 35 `partial`, and 111 `none` rows;
these totals include inherited claims and are not a fresh audit of all 206 rows.
The latest upstream rescaling and formal-power recurrence upgrades are retained;
the new Bernoulli formal-logarithm and Abel sources remain separately pending.
The upstream duplicate-crosswalk validator's eight regression tests passed at
that checkpoint. These are historical measurements, not current merged totals.

The present integration combines pinned upstream
`2ccc7f787becde416b234d40093876eac9f9c35e` with the preceding source/render
checkpoint. It preserves the incoming Newton reciprocal compilation receipt
and the prior Stirling complete-homogeneous and formal-power core receipts;
those receipts do not certify the merged wrappers or the complete dependency
graph. Fresh merged-source counts, structural checks, and PDF verification are
recorded separately by the publication owner. The second-kind recurrence and
Riordan rows retain their partial classifications for the explicit semantic
and inverse-construction gaps described below.

The subsequent Nörlund synchronization incorporates main through
`2ccc7f787becde416b234d40093876eac9f9c35e` and the source checkpoint
`16975fdfd`. The regenerated register has 207 results: 60 `Lean`, 35 `partial`,
and 112 `none`. `NorlundGeneralized` and the coefficient-base-change extension
of `BernoulliFormalLog` have independent source/API reviews but still await
compilation; no coverage upgrade is inferred from those reviews. Their human
proofs now include normalization, zero-ring boundaries, and degree zero.
The inherited PDF predates these latest source edits. PDF rebuilding remains
skipped in this work at the user's request, without discarding the upstream
render or claiming current render parity.

`NewtonReciprocal.lean` passed focused compilation on 2026-09-04 using
`lake env lean -o .lake/build/lib/lean/FabiusFunction/NewtonReciprocal.olean
Analysis/FabiusFunction/Lean/FabiusFunction/NewtonReciprocal.lean` (exit zero).
Its five public theorems have that inherited compiler receipt. The new
Stirling/Lagrange source and the merged reverse-row interfaces remain
source-reviewed and await compilation, including any missing prerequisites.
The merger deduplicates the reverse-row proof into `StirlingSecondReverseRow`
and derives the companion interfaces from it. No aggregate build is claimed.
At the preceding upstream synchronization, the cited-name and duplicate-name
structural audits passed: 3,439 distinct cited names resolved and there were no duplicate
declaration names. The facade audit found two missing upstream imports,
`AssociahedronFaceNumbers` and `PochhammerFalling`; both were restored. These
structural checks are not a fresh aggregate Lean build or current merge audit.
At that checkpoint all new modules had facade imports and contained no
`sorry`, `admit`, `axiom`, or `opaque` declarations. The register-generator mappings
preserved the new pending and compiled distinctions; both generator scripts passed
read-only syntax and mapping checks without rewriting the canonical document.

## Source correspondences inspected

Paths below are relative to `Analysis/FabiusFunction/Lean/FabiusFunction` unless
explicitly identified as Mathlib.

| Canonical claim | Source inspected | Audit conclusion |
| --- | --- | --- |
| `thm:merged-binomial-inversion` | `BinomialInversionEGF.lean`: `Fabius.egfA_eq_exp_mul_iff`, `Fabius.egfA_eq_altSeries_mul_iff`, `Fabius.egfA_eq_exp_mul_iff_egfA_eq_altSeries_mul` | Both formal generating-function directions are present over a commutative rational algebra. The old adjacent statement that this part is unformalized was stale. |
| `thm:merged-moment-cumulant` | `CumulantBellFormula.lean`: `Fabius.logOf_egfA`, `Fabius.cumulant_eq_cumulantSum` | The formal logarithm and closed partial-Bell expression are present, assuming the moment sequence starts with one. This does not identify these recurrence-defined polynomials with sums over actual set partitions. |
| `thm:merged-catalan-first-return` | `SquareRootSeries.lean`: `Fabius.sq_sqrtOf`, `Fabius.sqrt_unique`, `Fabius.sqrtOf_one_sub_four_X` | The square-root identity is present as a formal series identity with constant term one over a commutative rational algebra. Analytic branch and convergence statements remain separate obligations. |
| `thm:merged-riordan` | `ExponentialRiordan.lean`: `Fabius.expRiordan_action`, `Fabius.expRiordan_mul`, `Fabius.expRiordan_mul_inverse` | Action and multiplication are explicit. The inverse theorem is conditional: it assumes a compositional inverse and a suitable multiplicative reciprocal, and concludes one product is the identity. Construction of these data and the two-sided inverse assertion are not the statement of this declaration. |
| `thm:lagrange-burmann` | `LagrangeInversion.lean`: `Fabius.Lagrange.solution`, `Fabius.Lagrange.solution_eq`, `Fabius.Lagrange.coeff_solution_subst_derivative`, `Fabius.Lagrange.coeff_solution` | A solution and its coefficient formulas are constructed from a supplied inverse of the weight series. The reviewed source does not yet state solution uniqueness or the alternative coefficient formula. The phrase “unconditional” in its doc comments refers to constructing the solution; the supplied inverse hypothesis remains. |
| `thm:second-recurrence` | Mathlib `Combinatorics/Enumerative/Stirling.lean`: `Nat.stirlingSecond`, `Nat.stirlingSecond_succ_succ` | Mathlib defines the array recursively. Its counting description in a doc comment is not a theorem equating it with the cardinality of set partitions. The recurrence correspondence must not claim that missing bridge. |

## Editorial repairs identified in this audit

The documentation owner is incorporating these corrections in the current
milestone. Confirm the final TeX/PDF pair before calling the milestone published.

- Replace the frontmatter's obsolete assertion that no claim-level crosswalk
  exists, while retaining the distinction between human proofs and kernel checks.
- Remove repeated coefficient-rule crosswalk paragraphs.
- Reconcile the duplicated binomial-inversion and Catalan crosswalks: each had a
  newer positive correspondence immediately followed by an obsolete denial.
  Preserve the useful triangular-transform pointers when removing duplication.
- Update the moment-cumulant paragraph to acknowledge `CumulantBellFormula`.
- State the positive-radius neighborhood required by the analytic Cauchy rule.
- Handle the zero-order finite Darboux formula by the fundamental theorem of
  calculus before the cancellation proof for positive order.
- Restrict finite-field and integer implementation claims: the division-bearing
  logarithm, exponential, integration, and Lagrange recurrences require suitable
  units, unlike the division-free recurrences.
- Separate deterministic polynomial-grid certificates from probabilistic
  Schwartz--Zippel error bounds; a degree bound does not make a random test a
  deterministic proof.
- Replace the unspecified Watson hypotheses and unsupported exponent
  continuation in `thm:laplace-bell` with an explicit analytic endpoint theorem.
  Independent source review of the revised argument checked the positive-branch
  coordinate change, the polynomial continuation step, the transformed
  coefficients, and both local and tail remainder estimates.

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

The incoming `StirlingSecondReverseRowIdentity.lean` proof was independently
checked against the existing Stirling-transform and logarithmic-tail APIs.
The review checked the factorial kernel, coefficient
normalization, discarded zero prefix, finite-sum reindexing, binomial symmetry,
and transfer through the integers. It caught a mismatch between rational
subtraction in the logarithmic-tail denominator and natural subtraction in the
kernel helper; the author added an explicit rational normalization. The revised
incoming source had no further concrete blocker identified, but had not compiled.
That historical preflight does not certify the current merged implementation.

The merge retains `Fabius.second_reverse_row` and
`Fabius.second_reverse_row_ring_Icc` in `StirlingSecondReverseRow`, the latter
over any unital ring and with every nonnegative row index admitted.
The companion `StirlingSecondReverseRowIdentity` now reuses that proof for
`Fabius.second_reverse_row_range`, `Fabius.second_reverse_row_sum_ring`, and
the rational specialization `Fabius.second_reverse_row_sum`. The core source
proofs and these merged wrappers all remain pending compilation. Their
existence does not upgrade the combined second-kind reverse-recurrences row
from partial to Lean before compiler validation.

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
3. **Combinatorial semantics.** Build cardinality or weighted-enumerator bridges
   for set partitions, cycles, descents, and the recurrence-defined Bell and
   Stirling arrays. Algebraic recurrences alone cannot certify a counting
   interpretation. Use a shared finite-set decomposition API rather than proving
   every interpretation independently.
4. **Darboux analysis.** The corrected analytic-multiplier theorem explicitly
   handles polynomial exceptional exponents; the finite-smoothness subtraction
   theorem assumes a global decomposition and gives an explicit periodic boundary
   criterion. Source review found those two repairs mathematically coherent.
   Their gamma-ratio estimates, Cauchy bounds, convolution estimate, and boundary
   integration by parts still need actual Lean statements and proofs. No existing
   Darboux register row should be promoted merely because the human proof was
   repaired.
5. **Analytic and formal differential calculus.** Formal power-series composition
   and the two-factor formal Leibniz theorem are useful infrastructure, but do not
   prove the analytic Faà di Bruno theorem, the general multinomial product rule,
   or analytic inverse-derivative claims without explicit bridges.
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
