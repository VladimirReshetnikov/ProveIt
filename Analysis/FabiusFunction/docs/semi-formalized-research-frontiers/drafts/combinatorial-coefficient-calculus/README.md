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
| `Combinatorial_Coefficient_Calculus/` | **Canonical:** *Combinatorial Coefficient Calculus* — the evolving source and the retained upstream A4 PDF |

Upstream supplied a 208-page, 2,014,975-byte rebuilt PDF at its checkpoint. The
latest merged source includes subsequent Stirling and Nörlund changes, so that
retained PDF is a historical artifact and is not claimed to render the current
source. Further PDF building remains skipped in this work at the user's request. Standalone
checksum files are retired; provenance is kept
in Git and the source inventory, and the validator does not maintain or require
file digests.

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

## Current source-only Stirling overlay

The fixed-column second-kind Stirling theorem `thm:second-ogf` now separates
its formal-power-series content from scalar rational evaluation. Its
coefficient identity explicitly assumes `n >= k`; the formal proof identifies
two inverses of the same finite product, extracts the coefficient of the
finite product of geometric series, and then proves
`x^(k+1) * (1/x)↓(k+1) = ∏_{j=1}^k (1-jx)`. The falling-factorial spelling at
a scalar requires `x != 0`, and its reciprocal form also requires every
factor `1-jx` to be nonzero. The `k = 0`, `n = 0` empty-product case is
included.

The compiled zero-definition/eight-theorem
`StirlingCompleteHomogeneous.lean` surface contributes
`stirlingColumnOGF_eq_completeHomogeneousGeneratingSeriesOn`,
`stirlingSecond_add_eq_completeHomogeneousEvalOn`,
`stirlingSecond_eq_completeHomogeneousEvalOn_of_le`,
`stirlingSecond_add_eq_completeHomogeneousEval`,
`stirlingSecond_add_eq_eval_hsymm`, and
`stirlingSecond_add_eq_sum_finsuppAntidiag`. Its two companion declarations,
`pow_mul_descPochhammer_eval_inv_eq_prod_one_sub_natCast_mul` and
`prod_inv_one_sub_natCast_mul_eq_inv_pow_mul_descPochhammer_eval_inv`, cover
the scalar factorization and reciprocal spelling. Together they make
`thm:second-ogf` **Lean** with the corrected hypotheses. The retained PDF was
not rebuilt for this source-only overlay, so no PDF or checksum parity is
claimed for it.

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

All nine new or changed source leaves in this checkpoint have now passed direct,
sequential Lean elaboration, including `OrdinaryBellComposition`,
`OrdinaryBellMultinomial`, `AbelPolynomialSeries`, `BernoulliFormalLog`,
`RaneyNumbers`, and `AssociahedronFaceNumbers`.

The merged register contains 207 rows. The retained formal-power result and
ordinary-composition multiplicity theorem are Exact, as is the Abel proposition;
the Raney and associahedron arithmetic has the narrower scope recorded below,
and Riordan inversion is Partial because its inverse data are assumed rather
than constructed. The live totals are therefore **69 Lean, 35 partial, and 103
none**. The new Lagrange, Raney, Nörlund, Newton, grid/CRT, Pochhammer, and
Stirling leaves have all passed direct sequential Lean elaboration; the register
still distinguishes exact formal algebra from its remaining analytic and
combinatorial obligations.
Earlier classifications are inherited; these counts are a coverage register,
not a fresh rebuild of every proof. Structural/provenance validation covers 207
adjacent proofs, 27 disposition records, and six original-source inventory
rows. PDF rebuilding remains deferred at the user's request.

The same-day upstream crosswalk connects the Bell normalization and unit-series
coefficient formulas to `UnitSeriesBellCoefficients`; its labelled-set partition
interpretation remains unformalized. That partial result is included in the
register totals above.

## Formal-power recurrence (2026-09-04)

`UnitSeriesPowerRecurrence` supplies three checked theorems. Over any
commutative ring, the differential equation `A C' = α A' C` implies
`n a₀ cₙ = Σ_{j=1}^n ((α+1)j−n) aⱼ cₙ₋ⱼ`, without assuming `a₀` is
invertible. Over a commutative rational algebra with `a₀=1`, formal binomial
substitution gives `C=A^α`, satisfies that differential equation, and yields
the manuscript's triangular coefficient algorithm. Its proof and crosswalk
now cover all three clauses of `alg:merged-exp-log-power` exactly.

The proof uses the Euler derivative `z d/dz` to keep degree indices aligned,
then separates the constant-coefficient term of the Cauchy product. The
canonical source includes that complete argument, including the constant
term and inductive uniqueness of the resulting coefficient sequence. This
is formal algebra; no analytic branch choice or convergence claim is made.

## Coefficient-calculus campaign (2026-09-04)

The new leaf modules supply the public theorem statements listed in the
register, with complete human proofs and exact declaration names in the
manuscript. `NewtonReciprocal`, `StirlingSymmetricFunctions`,
`LagrangeInversionUniqueness`, and `StirlingSecondReverseRowIdentity` have all
passed direct sequential Lean compilation, including the actual truncated
Newton update and the integer-transport reverse-row identity. The register
preserves the remaining claim-level distinctions.
The two second-kind symmetric-function formulas are shared with the compiled
upstream `StirlingCompleteHomogeneous` module; their duplicate implementations
were removed from this campaign's leaf.

The campaign also repairs the Laplace theorem with explicit analytic endpoint
hypotheses and full remainder estimates, removes contradictory duplicate
crosswalks, and corrects boundary cases and coefficient-ring assumptions.
The brief [campaign status](Combinatorial_Coefficient_Calculus/FORMALIZATION_STATUS.md)
records remaining obligations without duplicating the canonical claim register.

## Additional formal-series checkpoints (2026-09-04)

`ExponentialRescaling` has passed a focused build. Its four public lemmas give
the rescaling chain rule over every commutative semiring and exponential
specializations over every commutative rational algebra. They replace the
rational-only helpers in `NorlundDiagonal` without changing their names. The
manuscript supplies full coefficient proofs and an exact crosswalk.

`AbelPolynomialSeries` constructs a solution over every commutative rational
algebra, derives coefficients for every solution, and proves the full EGF and
binomial identity including degree zero; this makes the complete Abel
proposition Exact. The new
`BernoulliFormalLog` source derives the rational formal logarithm of the
Bernoulli kernel using the existing recurrence-to-logarithm bridge. Its
coefficient formula separates degree zero and preserves the distinction between
the two degree-one Bernoulli conventions. This exactly covers the internal
logarithm calculation in the Nörlund proof; that internal result alone does not
promote the arbitrary-order row.

`RaneyNumbers` proves the displayed coefficient formula, including degree zero,
for its constructed Lagrange solution; the manuscript's arbitrary-solution
scope still lacks a uniqueness or transfer theorem. `AssociahedronFaceNumbers`
proves the dissection, face-array, and Narayana-row arithmetic, including
integrality and boundary values, but deliberately defines those arrays without
constructing dissections, a face lattice, or the face-to-`h` transform. Those
four rows are therefore Partial rather than Exact.

The human moment-cumulant proof now states its normalization and positive-degree
boundaries explicitly, with formal logarithm identities separated from the
still-open set-partition interpretation. The Nörlund proof now derives the
logarithmic coefficients without dividing by the nonunit formal variable.

## Ordinary composition multiplicities (2026-09-04)

`OrdinaryBellMultinomial` gives a finite profile set for the multiplicities of
parts of sizes `1,…,n`, characterizes its two constraints, and proves the
multinomial formula for ordinary partial Bell polynomials over every
commutative semiring. Its composition corollary works over every commutative
ring and includes degree zero: the unique empty profile gives `c₀=a₀`.
Together with the upstream finite-degree locality theorem
`ordPartialBell_congr_of_le`, these are five public declarations. The current
merged source census is 987 modules and 12,207 explicit declarations after the
post-merge Raney addition.

Direct sequential Lean checks passed for all nine new or changed modules in
this merge, the three ordinary-composition callers, and the complete facade
import check against the compiled dependency cache. The Raney proof was
repaired before this check; its derivative, scalar-coefficient extraction,
and nonzero-factor cancellation now elaborate. This is a focused validation,
not a fresh build of the whole corpus. At that checkpoint the canonical
validator passed with zero errors or warnings, and crosswalk regeneration
applied no pending remarks.

## Arbitrary-order Nörlund synchronization (2026-09-04)

The compiler-checked `NorlundGeneralized` source constructs actual polynomials
at every scalar order over a commutative rational algebra. Its API includes the
full EGF, Appell derivative, translation, convolution, natural-order polynomial
compatibility, explicit cumulants, and the complete Bell formula.
`BernoulliFormalLog` now compiler-verifiably transports the logarithm and its
coefficients along arbitrary coefficient ring homomorphisms and shares the
kernel normalization lemma. This makes `lem:merged-log-base-change` Exact and
strengthens both Nörlund crosswalks without promoting their combined rows:
general-order finite differences and the literal multiplicity-vector expansion
remain separate formalization obligations. Analytic convergence likewise
remains outside these formal-series declarations.

The human exposition gives the normalized complex logarithm construction on its
disk separately from the formal algebra, states the coefficient-base-change
lemma with proof, and includes the degree-zero multiplicity convention.
