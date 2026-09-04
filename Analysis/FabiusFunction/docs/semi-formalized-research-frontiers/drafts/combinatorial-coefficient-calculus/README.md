# combinatorial-coefficient-calculus

Canonical consolidation of six combinatorial coefficient-calculus and inversion
manuscripts received on 2026-09-01. Each arrival supplied one flat LaTeX/PDF
pair. The ZIP CRCs, member paths, and member types were checked before
extraction; at intake, the filed source and PDF bytes were identical to their
ZIP members.

**The consolidation is complete.** `Combinatorial_Coefficient_Calculus/` is the
single surviving package, and the five donor directories have been deleted now
that every source, topic, and claim row of the disposition ledger carries a
completed disposition. This was deliberately not a concatenation: 394 labels
occurred in more than one source, and the common material is retained once,
with the strongest correct hypotheses and one complete proof. A second proof
survives only where it exposes a different mechanism.

The consolidation boundary is recorded in
[`PROVENANCE.md`](Combinatorial_Coefficient_Calculus/PROVENANCE.md), the six
original sources and their immutable Git recovery locators in
[`SOURCE_INVENTORY.csv`](Combinatorial_Coefficient_Calculus/SOURCE_INVENTORY.csv),
and the topic/claim decisions in
[`SOURCE_DISPOSITION.csv`](Combinatorial_Coefficient_Calculus/SOURCE_DISPOSITION.csv).
The standard-library
[`validate_canonical.py`](Combinatorial_Coefficient_Calculus/validate_canonical.py)
checks LaTeX structure, labels, references, citations, proof pairing, exact
source coverage, Git object availability, and the one-publication layout;
run it with `--final`, which is the
mode this package is now expected to pass.

| Directory | Document |
| --- | --- |
| `Combinatorial_Coefficient_Calculus/` | **Canonical:** *Combinatorial Coefficient Calculus* — synchronized 213-page A4 PDF, 2,063,614 bytes, rebuilt on 2026-09-04 after integrating main `da90f69d1` |

The current source has 209 adjacent proofs and a
66 Lean / 35 partial / 108 none register. It measures 11,290 lines and
555,974 UTF-8 bytes, with 712 labels and 960 references. Three strict pdfLaTeX
passes succeeded, and six changed/register/index pages were visually inspected;
no whole-volume page-by-page review is claimed. One readable 28.0023 pt overfull
box at the inline `HasFTaylorSeriesUpToOn.comp` name on page 115 is deferred to
the requested dedicated layout pass. Full checkpoint measurements and
the distinction between inherited compiler receipts and pending source proofs
are recorded in `Combinatorial_Coefficient_Calculus/FORMALIZATION_STATUS.md`.
Standalone checksum files are retired; provenance is kept in Git and the source
inventory, and the validator does not maintain or require file digests.

## What the final merge changed

The last pass was driven by a label- and formula-level inventory of all six
sources rather than by reading order. Chapter `ch:merged-concordance`,
section "Closure of the merge", carries the in-document record. In summary:

- **The manuscript did not compile.** The shared-notation migration had left
  eight calls to catalogue macros whose expansion already ends in a script
  group followed directly by a prime or an exponent — for example
  `\TouchardPolynomial{n}'`, where the macro expands to
  `\mathsf{T}^{\mathrm{Tou}}_{n}`. Each is a fatal TeX "Double superscript"
  error.
- **A withdrawn claim became a theorem.** All six arrivals asserted
  `B_n < (0.792 n / log(n+1))^n` for every `n >= 1` without proving either the
  tail or the finite range, and the consolidation had demoted it to a remark.
  It is a theorem of Berend and Tassa (2010) and is now proved in both ranges:
  the tail from a new monotonicity lemma for the coefficient majorant, and
  `n <= 38` from the inequality between positive integers
  `B_n A_n^n < (792000 n)^n` with `A_n = ceil(10^6 log(n+1))`, which contains no
  irrational quantity at all.
- **An existing proof rested on an unstated fact.** The polygamma series were
  derived by logarithmically differentiating a Weierstrass product for
  `1/Gamma` that appeared nowhere else in the manuscript. Euler's limit and
  that product are now proved from the integral definition of `Gamma`, via the
  Beta integral.
- **Thirteen further donor-only results were merged**, each with a proof
  written for this text and each checked against an independent symbolic or
  exact-integer computation before insertion.
- **Notation was made uniform.** Around 180 further sites still spelled
  catalogue symbols by hand, including an italic imaginary unit next to an
  upright `e` inside one exponent. The document now follows
  `FabiusFunction_Mathematical_Notation_Catalogue` throughout.

## Integrated Stirling proof sources

The fixed-column second-kind Stirling theorem `thm:second-ogf` now separates
its formal-power-series content from scalar rational evaluation. Its
coefficient identity explicitly assumes `n >= k`; the formal proof identifies
two inverses of the same finite product, extracts the coefficient of the
finite product of geometric series, and then proves
`x^(k+1) * (1/x)↓(k+1) = ∏_{j=1}^k (1-jx)`. The falling-factorial spelling at
a scalar requires `x != 0`, and its reciprocal form also requires every
factor `1-jx` to be nonzero. The `k = 0`, `n = 0` empty-product case is
included.

The eight upstream theorem bodies in `StirlingCompleteHomogeneous.lean` contribute
`stirlingColumnOGF_eq_completeHomogeneousGeneratingSeriesOn`,
`stirlingSecond_add_eq_completeHomogeneousEvalOn`,
`stirlingSecond_eq_completeHomogeneousEvalOn_of_le`,
`stirlingSecond_add_eq_completeHomogeneousEval`,
`stirlingSecond_add_eq_eval_hsymm`, and
`stirlingSecond_add_eq_sum_finsuppAntidiag`. Its two companion declarations,
`pow_mul_descPochhammer_eval_inv_eq_prod_one_sub_natCast_mul` and
`prod_inv_one_sub_natCast_mul_eq_inv_pow_mul_descPochhammer_eval_inv`, cover
the scalar factorization and reciprocal spelling. Together they make
`thm:second-ogf` **Lean** with the corrected hypotheses. This is an inherited
build classification, not a new compiler run in this worktree: commit
`584ec4e68` records warning-free focused builds of
`CompleteHomogeneousGenerating`, `StirlingOrdinaryGF`, and
`StirlingCompleteHomogeneous`, together with the eight-declaration axiom
audit. Its Stirling source is byte-identical to the version received at
`ebe17b063`. The merged compatibility, explicit-tuple, and Bell power-sum
wrappers are additional source work and still await compilation.

The same distinction applies to `UnitSeriesPowerRecurrence`: commit
`a1f579d84` records sequential elaboration of the upstream power module and
facade, and its power-module source is byte-identical to that received at
`ebe17b063`. The upstream declarations
`coeff_recurrence_of_mul_derivative_eq`,
`mul_derivative_fallingSeries_subst_sub_one`, and
`coeff_fallingSeries_subst_sub_one_recurrence` supply the exact generic ODE
and normalized-power crosswalks. Their inherited verification does not
extend to the merged Euler-coefficient and compatibility wrappers or prove
that the complete merged dependency graph compiles.

## What this package does not claim

The manuscript is research-frontier mathematical writing. Its theorem and proof
environments are human-readable mathematics, not evidence of Lean verification.
The section "Lean formalization register" states, per result, what is formalized
and what is not; it is maintained separately from this consolidation.

## Formalization checkpoints (2026-09-04)

The `AppellSequence` extension has passed direct, sequential Lean elaboration:
eleven public lemmas provide weighted binomial translation,
convolution transport, cancellation, and inversion. The manuscript gives their
complete human proofs and exact declaration crosswalks. Three private rational
helpers in `FinitePrefixThueMorseCollapse` were replaced by the shared API; that
caller refactor has now passed its own direct Lean check as well.

At incoming main checkpoint `28de4e51c`, the register contained 207 rows:
62 marked Lean, 35 partial, and 110 without a compiler-verified counterpart.
The grid and CRT certificates retain two compiler-backed entries from
`5a685136b`; this is not a fresh build of the whole corpus. That commit also
corrected a stale status distribution in the earlier 204-row header.
The incoming structural/provenance validator passed with 207 adjacent
proofs, 27 disposition records, and six original-source inventory rows. PDF
rebuilding was deferred in that earlier session. These are historical upstream
measurements, not totals for the present merged manuscript.

The same-day upstream crosswalk connects the Bell normalization and unit-series
coefficient formulas to `UnitSeriesBellCoefficients`; its labelled-set partition
interpretation remains unformalized. That partial result is included in the
register totals above.

## Stirling and formal-power source checkpoint (2026-09-04)

The source implementation now includes the second-kind reverse-row recurrence
over arbitrary rings, the complete-homogeneous identification of Stirling
columns over commutative semirings, an explicit weak-composition reindexing,
and a division-free Bell/power-sum consequence. A separate reusable
coefficient-extraction theorem gives the formal-power recurrence from its
differential equation, with no normalization needed for the general ring form.
The manuscript supplies complete human proofs and maps every new public
declaration to its mathematical statement.

These additions passed independent mathematical and exact-library source
reviews before compilation. Other worktrees held the machine-wide Lean build
slot during that checkpoint. Before integrating the upstream compiled Stirling
and power cores described above, the register had 206 rows:
58 marked Lean, 34 partial, and 114 without a
compiler-verified counterpart. The two new rows have human proofs and pending
Lean source implementations; earlier statuses are inherited, not freshly
validated by an aggregate build.

At that checkpoint the final structural/provenance validator passed with 206
adjacent proofs, 27 disposition records, and six original-source inventory
rows. The source was 10,780 lines / 523,775 UTF-8 bytes. The rebuilt 207-page PDF uses Libertinus text
and Computer Modern mathematics. Validation includes focused visual inspection
of the revised recurrence, coefficient, crosswalk, and register pages; it is
not a claim of a fresh page-by-page audit of the whole monograph.

The merged near-diagonal Bell formula now caps the nonsingleton count by the
total degree before forming powers of the singleton weight. This removes
undefined negative powers from nominally zero terms. Its multiplicity proof
also now includes the missing singleton factorial; the displayed edge formulas
state the corresponding omission and degree conventions explicitly.

The standard-library script
`Analysis/FabiusFunction/scripts/verify_stirling_coefficient_identities.py`
performs exact finite regressions: 255 reverse-row cases in two summation
ranges, 49 weak-composition cases (1,716 tuples), 49 Bell power-sum cases,
and 462 near-diagonal Bell cases over seven integer/rational weight families.
The last set includes 198 cases with zero singleton weight and 210 cases where
the new summation cap shortens the range. All pass. These computations are
regression evidence, not infinite-domain proofs or Lean compilation results.

## Coefficient-calculus campaign (2026-09-04)

The incoming campaign added four leaf modules, with complete human proofs and
exact declaration names in the manuscript. `NewtonReciprocal` has an inherited
focused Lean compilation receipt, including the actual truncated update.
`StirlingSymmetricFunctions`, `LagrangeInversionUniqueness`, and
`StirlingSecondReverseRowIdentity` have received independent source/API reviews;
their compiler validation is pending. The register preserves that distinction.
The two second-kind symmetric-function formulas are shared with the compiled
upstream `StirlingCompleteHomogeneous` module; their duplicate implementations
were removed from this campaign's leaf.

The reverse-row merge likewise preserves the existing
`Fabius.second_reverse_row` and all-degree `Fabius.second_reverse_row_ring_Icc`
interfaces in `StirlingSecondReverseRow`. The companion
`StirlingSecondReverseRowIdentity` contributes `Fabius.second_reverse_row_range`,
`Fabius.second_reverse_row_sum_ring`, and the rational
`Fabius.second_reverse_row_sum` by reusing that core. These merged row proofs
and wrappers remain pending compilation; no duplicate proof is retained as
independent validation.

The campaign also repairs the Laplace theorem with explicit analytic endpoint
hypotheses and full remainder estimates, removes contradictory duplicate
crosswalks, and corrects boundary cases and coefficient-ring assumptions.
The second-kind recurrence and Riordan rows remain partial: the former lacks
the set-partition counting bridge, while the latter supplies a conditional
one-sided inverse law rather than the full inverse construction.
The brief [campaign status](Combinatorial_Coefficient_Calculus/FORMALIZATION_STATUS.md)
records remaining obligations without duplicating the canonical claim register.

## Integrated Abel and moment-cumulant checkpoint (2026-09-04)

`ExponentialRescaling` has passed a focused build. Its four public lemmas give
the rescaling chain rule over every commutative semiring and exponential
specializations over every commutative rational algebra. They replace the
rational-only helpers in `NorlundDiagonal` without changing their names. The
manuscript supplies full coefficient proofs and an exact crosswalk.

The compiled `AbelPolynomialSeries` source constructs a solution over every
commutative rational algebra, derives coefficients for every solution, and
proves the full EGF and binomial identity including degree zero. The new
`BernoulliFormalLog` source derives the rational formal logarithm of the
Bernoulli kernel using the existing recurrence-to-logarithm bridge. Its
coefficient formula separates degree zero and preserves the distinction between
the two degree-one Bernoulli conventions. The Abel target passed a focused
build; `BernoulliFormalLog` and the complete affected-dependent closure have
not been rebuilt for this checkpoint. Independent source reviews are not
compiler validation, and no further register row is promoted here.

`GridEvaluationCertificate` and `IntegerCRTCertificate` supply nine public
theorems with inherited warning-free focused-build and standard-axiom receipts
in `5a685136b`. Both module sources are unchanged at incoming `17156aa2a`;
this is not a fresh compilation of the merged tree. Their full human
statements and proofs remain grouped in the two existing certificate theorems:
grid uniqueness over any integral domain, and product-divisibility plus
zero/equality certificates for signed pairwise-coprime integer moduli.
The zero test uses the stronger full-product bound. The adjacent discussion now
distinguishes probabilistic identity testing from exact grid certificates.

The human moment-cumulant proof now states its normalization and positive-degree
boundaries explicitly, with formal logarithm identities separated from the
still-open set-partition interpretation. The Nörlund proof now derives the
logarithmic coefficients without dividing by the nonunit formal variable.
The new `NorlundGeneralized` source constructs actual polynomials at every
scalar order over a commutative rational algebra. Its source-reviewed API
includes the full EGF, Appell derivative, translation, convolution, natural-order
polynomial compatibility, explicit cumulants, and the complete Bell formula.
`BernoulliFormalLog` now transports the logarithm and its coefficients along
arbitrary coefficient ring homomorphisms and shares the kernel normalization
lemma. These extensions have not yet compiled, so no corresponding coverage
promotion is claimed. General-order finite differences, the literal
multiplicity-vector expansion, and analytic convergence remain separate
formalization obligations.

The human exposition gives the normalized complex logarithm construction on its
disk separately from the formal algebra, states the coefficient-base-change
lemma with proof, and includes the degree-zero multiplicity convention.
