# Formalization campaign status

This is a source-review handoff for the campaign begun on 2026-09-04. The
canonical claim register is the **Lean formalization register** section of
`Combinatorial_Coefficient_Calculus.tex`; this file does not reproduce its rows.
Mathematical statements and proofs belong in the TeX/PDF pair. The register's
status words are recorded correspondence claims, not a fresh compilation receipt.

## Inventory and evidence boundary

The initial source snapshot contains 201 theorem-like environments: 150 theorems,
26 corollaries, 12 propositions, 6 lemmas, and 7 algorithms. Its register has 201
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
`c668cb96362acbae8b89950102b8ea361102a73f`. Its source validator passes with
206 theorem-like items and adjacent proofs, 27 dispositions, and six immutable
source-inventory rows. The obsolete live checksum ledger was retired as upstream
intended. At that checkpoint the register had 60 `Lean`, 35 `partial`, and 111 `none` rows;
these totals include inherited claims and are not a fresh audit of all 206 rows.
The latest upstream rescaling and formal-power recurrence upgrades are retained;
the Bernoulli formal-logarithm and Abel sources were compiled in the following
checkpoint and are reflected in the current register rather than left pending.
The upstream duplicate-crosswalk validator's eight regression tests pass.

The subsequent Nörlund synchronization incorporates the intermediate main
checkpoint `2ccc7f787becde416b234d40093876eac9f9c35e`, source checkpoint
`16975fdfd`, and current pinned main
`b50d5349ec2db42d056fe3a6f6c7286365ff77ed`. The pre-sweep register at that
source checkpoint had 207 results: 64 `Lean`, 38 `partial`, and 105 `none`.
After the focused checks and exact symmetric-function promotions, the live
register has 69 `Lean`, 35 `partial`, and 103 `none`. `NorlundGeneralized` and the coefficient-base-change extension
of `BernoulliFormalLog` have now passed focused compiler validation. The latter
makes `lem:merged-log-base-change` Exact; the former strengthens the two
Nörlund rows while their specifically named residual gaps remain Partial. Their
human proofs include normalization, zero-ring boundaries, and degree zero. The
current merged source census is 987 modules and 12,207 explicit declarations.
The inherited 208-page, 2,014,975-byte PDF predates these latest source edits.
PDF rebuilding remains skipped in this work at the user's request, without
discarding the upstream render or claiming current render parity.

All affected leaves passed focused compilation on 2026-09-04 using
`lake env lean -o .lake/build/lib/lean/FabiusFunction/NewtonReciprocal.olean
Analysis/FabiusFunction/Lean/FabiusFunction/NewtonReciprocal.lean` (exit zero),
with the same single-module driver applied to the remaining affected closure.
All 36 modules in that closure are compiler-checked; no aggregate build is
claimed.
After the latest synchronization, the cited-name and duplicate-name structural
audits pass: 3,500 distinct cited names resolve and there are no duplicate
declaration names. The facade audit found two missing upstream imports,
`AssociahedronFaceNumbers` and `PochhammerFalling`; both were restored. These
structural checks are not a fresh aggregate Lean build. All new modules have facade imports and contain no
`sorry`, `admit`, `axiom`, or `opaque` declarations. The register-generator mappings
preserve the new pending and compiled distinctions; both generator scripts passed
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
| `thm:lagrange-burmann` | `LagrangeInversion.lean` and `LagrangeInversionUniqueness.lean`: `Fabius.Lagrange.solution`, `Fabius.Lagrange.solution_eq`, `Fabius.Lagrange.coeff_solution_subst_derivative`, `Fabius.Lagrange.coeff_solution`, `Fabius.Lagrange.eq_solution_of_eq_X_mul_subst`, `Fabius.Lagrange.existsUnique_solution`, `Fabius.Lagrange.existsUnique_of_isUnit_constantCoeff`, `Fabius.Lagrange.coeff_jacobian_mul`, `Fabius.Lagrange.coeff_subst_alt`, `Fabius.Lagrange.coeff_solution_subst_alt` | The construction, uniqueness, Jacobian identity, and alternative coefficient formula are compiler-checked. Construction and uniqueness work over a commutative ring when the weight constant coefficient is a unit; the coefficient formulas use a commutative rational algebra and `1≤n`. Formal power-series algebra is covered; analytic convergence and residue language are not asserted. |
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
