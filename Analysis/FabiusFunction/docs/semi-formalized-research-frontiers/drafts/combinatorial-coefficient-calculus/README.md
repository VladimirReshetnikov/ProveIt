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
run it with `--final`, which is the mode this package is expected to pass at a
publication checkpoint.

| Directory | Document |
| --- | --- |
| `Combinatorial_Coefficient_Calculus/` | **Canonical:** *Combinatorial Coefficient Calculus* — the evolving source and the retained upstream A4 PDF |

Upstream supplied a rebuilt PDF at its checkpoint. The merged source includes
subsequent Stirling, Nörlund, Bell, and Cauchy-polynomial changes, so that
retained PDF is historical and is not claimed to render the current source.
Further PDF building is deferred at the user's request. Standalone checksum
files are retired; provenance is kept in Git and the source inventory, and the
validator does not maintain or require file digests.

## Additional exact correspondences retained in the merge

Crosswalk work closes the full Cauchy-polynomial theorem block: the
formal and real interval integrals, reflection, and generic generating-function
and addition laws are now represented, with the latter two valid after
evaluation in any commutative rational algebra. The analytic convergence and
branch assertion attached to the generating function remains outside that
formalized theorem block. The second-kind reverse-row recurrence is now
machine checked in a division-free integral form, including its zero boundary
case beyond the range used by the displayed human formula; the separately
merged unrestricted rational-index source identity remains pending validation
under its collision-free declaration name. The ordinary versus
exponential Bell normalization now has both its rational ratio form and a
denominator-free commutative-semiring form, together with functoriality and the
upper variable-support cutoff. The sharpness witness for that cutoff, the
general Bell near-diagonal reduction, its two-block case, and the higher
subdiagonals remain human-only or partial as recorded in the register.

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
not rebuilt for this source-only overlay, so no current render parity is
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

The document's generated register is the single source of current row counts
and Lean/partial/none classifications. Its inherited formal-power, Stirling,
Newton, and certificate checkpoints are not a fresh compilation of the whole
corpus. The final structural/provenance validator checks the advertised totals
against the actual rows as well as adjacent proofs, the 27 disposition records,
and six original-source inventory rows. PDF building remains skipped for this
source-only synchronization.

The same-day upstream crosswalk connects the Bell normalization and unit-series
coefficient formulas to `UnitSeriesBellCoefficients`. The subsequent incoming
`BellSetPartitions` independently supplies the weighted labelled-set
interpretation and the Stirling block-count specialization; its compiled
status is recorded by upstream commit `dd554e5a8`, not a fresh local replay.
The prescribed-block-size type count remains a separate obligation.

## Coefficient-calculus campaign (2026-09-04)

Four new leaf modules supply seventeen public theorem statements, with complete
human proofs and exact declaration names in the manuscript. `NewtonReciprocal`
has passed focused Lean compilation, including the actual truncated update.
`StirlingSymmetricFunctions`, `LagrangeInversionUniqueness`, and
`StirlingSecondReverseRowIdentity` have received independent source/API reviews;
their compiler validation is pending. The register preserves that distinction.
The two second-kind symmetric-function formulas are shared with the compiled
upstream `StirlingCompleteHomogeneous` module; their duplicate implementations
were removed from this campaign's leaf.

The campaign also repairs the Laplace theorem with explicit analytic endpoint
hypotheses and full remainder estimates, removes contradictory duplicate
crosswalks, and corrects boundary cases and coefficient-ring assumptions.
The brief [campaign status](Combinatorial_Coefficient_Calculus/FORMALIZATION_STATUS.md)
records remaining obligations without duplicating the canonical claim register.

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

## Additional formal-series checkpoints (2026-09-04)

`ExponentialRescaling` has passed a focused build. Its four public lemmas give
the rescaling chain rule over every commutative semiring and exponential
specializations over every commutative rational algebra. They replace the
rational-only helpers in `NorlundDiagonal` without changing their names. The
manuscript supplies full coefficient proofs and an exact crosswalk.

The source-reviewed `AbelPolynomialSeries` module constructs a solution over every
commutative rational algebra, derives coefficients for every solution, and
proves the full EGF and binomial identity including degree zero. The new
`BernoulliFormalLog` source derives the rational formal logarithm of the
Bernoulli kernel using the existing recurrence-to-logarithm bridge. Its
coefficient formula separates degree zero and preserves the distinction between
the two degree-one Bernoulli conventions. The Abel target passed a focused
build; `BernoulliFormalLog` and the complete affected-dependent closure have
not been rebuilt for this checkpoint. Independent source reviews are not
compiler validation, and no further register row is promoted here.

`GridEvaluationCertificate` and `IntegerCRTCertificate` supply nine compiled
public theorems, each with only the standard project axioms. Their full human
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
The next source checkpoint adds the arbitrary-order finite-difference law in
successor and all-degree forms, including zero and negative orders.
`BernoulliFormalLog` now transports the logarithm and its coefficients along
arbitrary coefficient ring homomorphisms and shares the kernel normalization
lemma. These extensions have not yet compiled, so no corresponding coverage
promotion is claimed. The new `BellCompletePartitions` leaf shares the existing
complete-Bell/weighted-partition dictionary to state the literal multiplicity
sum, its normalized coefficient form, and its field-division form; it assumes
nothing about the unused zeroth input. The two new Nörlund specializations
reuse that generic formula. These seven new public theorems are source-reviewed
and still await compilation. The coefficient-algebra diagonal transport and
analytic convergence remain separate formalization obligations.

The human exposition gives the normalized complex logarithm construction on its
disk separately from the formal algebra, states the coefficient-base-change
lemma with proof, and includes the degree-zero multiplicity convention.
The generic Bell multiplicity lemma now carries the common complete human
proof; the Nörlund section specializes it instead of repeating that argument.
The source validator's fourteen regression tests pass, including the inherited
advertised-register-total checks. These are structural checks, not Lean builds.
