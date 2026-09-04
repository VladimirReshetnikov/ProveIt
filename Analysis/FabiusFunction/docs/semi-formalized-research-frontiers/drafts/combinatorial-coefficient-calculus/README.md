# combinatorial-coefficient-calculus

Canonical consolidation of six combinatorial coefficient-calculus and inversion
manuscripts received on 2026-09-01. Each arrival supplied one flat LaTeX/PDF
pair. ZIP CRCs, member paths, and member types were checked before extraction;
at intake the filed source and PDF bytes were identical to their ZIP members.

The archival consolidation is complete: `Combinatorial_Coefficient_Calculus/`
is the single surviving package, and the five donor directories were retired
after all source, topic, and claim disposition rows were completed. The
mathematical formalization campaign remains open. Its canonical source evolves
as proofs are repaired, strengthened, and matched with Lean declarations.

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
| [Canonical TeX](Combinatorial_Coefficient_Calculus/Combinatorial_Coefficient_Calculus.tex) and [PDF](Combinatorial_Coefficient_Calculus/Combinatorial_Coefficient_Calculus.pdf) | Mathematical exposition and the single in-document Lean claim register. |
| [Campaign status](Combinatorial_Coefficient_Calculus/FORMALIZATION_STATUS.md) | Current compilation, review, rendering, and remaining-work receipts. |
| [Provenance](Combinatorial_Coefficient_Calculus/PROVENANCE.md) | Consolidation boundary and immutable recovery procedures. |
| [Source inventory](Combinatorial_Coefficient_Calculus/SOURCE_INVENTORY.csv) | Six original sources and their immutable Git recovery locators. |
| [Source dispositions](Combinatorial_Coefficient_Calculus/SOURCE_DISPOSITION.csv) | Editorial decisions for source, topic, and claim records. |
| [Canonical validator](Combinatorial_Coefficient_Calculus/validate_canonical.py) | Structural and provenance checks; this package is expected to pass `--final`. |

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
machine checked in a division-free integral form and, by transport from the
integers, over every commutative ring, including its zero boundary case beyond
the range used by the displayed human formula. The separately merged
unrestricted rational-index source identity remains pending validation. The ordinary versus
exponential Bell normalization now has both its rational ratio form and a
denominator-free commutative-semiring form, together with functoriality and the
upper variable-support cutoff. The sharpness witness for that cutoff, the
general Bell near-diagonal reduction, its two-block case, and the higher
subdiagonals remain human-only or partial as recorded in the register.

Standalone checksum ledgers are retired. Provenance is preserved in Git and the
source inventory, and the validator does not maintain or require live-file
digests. Its checks cover structure, labels, references, citations, proof pairing,
source coverage, Git object availability, dispositions, and publication layout.
They do not compile Lean or establish mathematical correctness.

## Consolidation history

The consolidation used a label- and formula-level inventory of all six inputs.
The inventory found 394 labels occurring in more than one source. Closely
related material was grouped, common statements retained once, and alternate
proofs preserved where they explain a different mechanism. The manuscript's
concordance chapter contains the mathematical contribution map.

The historical consolidation also repaired fatal TeX superscript errors left
by the notation migration, expanded the Bell upper-bound proof and its finite
verification, supplied missing analytic prerequisites for the polygamma
discussion, integrated thirteen donor-only results, and normalized notation.
These editorial and human-proof changes do not by themselves constitute Lean
formalization.

## Current coefficient-calculus campaign

The six new leaves contain **25 public theorems: five compiled and twenty
pending compilation**. `NewtonReciprocal` has passed focused compilation.

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

At that earlier checkpoint, the merged register contained 207 rows: 68 marked Lean, 35 partial, and 104
without a compiler-verified counterpart. The grid and CRT certificates, the
Bell set-partition interpretation, and the retained Bell, Cauchy, and reverse-row
crosswalks contribute compiler-backed entries alongside the incoming
classifications; this is not a fresh build of the whole corpus. The source-level
validator accounts for 210 adjacent proofs, 27 disposition records, and six
original-source inventory rows. The retained PDF is historical; this merge follows the
user-requested PDF deferral, so current render parity is not claimed.

The Bell normalization and unit-series coefficient formulas are connected to
`UnitSeriesBellCoefficients`; `BellSetPartitions` separately supplies the exact
weighted labelled-set partition interpretation. The finer per-type coefficient
count remains outside that theorem, as recorded in the register.

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
manuscript. Upstream focused receipts record direct sequential compilation of
`NewtonReciprocal`, `StirlingSymmetricFunctions`, `LagrangeInversionUniqueness`,
and `StirlingSecondReverseRowIdentity`, including the actual truncated Newton
update and the integer-transport reverse-row identity. This merge does not rerun
those Lean commands; the register preserves the more precise claim-level
boundaries. The two second-kind symmetric-function formulas are shared with the
compiled upstream `StirlingCompleteHomogeneous` module, and their duplicate
implementations were removed from this campaign's leaf.

The first Lagrange uniqueness compilation attempt reached the default heartbeat
limit while inferring an inverse witness. The correction supplies explicit
proof data and awaits retry; the statement and heartbeat limit are unchanged.
Separately, thirteen existing helper/existence theorems in `LagrangeInversion`
now have weaker coefficient-ring assumptions and have passed direct compilation.
They are not counted among the twenty-five new theorems.

The manuscript currently contains 210 theorem-like entries: **77 `Lean`,
53 `partial`, and 80 `none`**. The latest claim audit corrected overclaims in
the Abel and Fréchet crosswalks and confirmed the second-kind Stirling
set-partition counting interpretation through
`BellSetPartitions.card_setPartitions`. That correspondence uses upstream
validation evidence; this campaign has not freshly compiled the counting
module. The in-document register remains authoritative, and a compiled source
module does not automatically certify every assertion in a broader theorem.

The campaign repairs the Laplace theorem's analytic assumptions and remainder
proof, removes contradictory duplicate crosswalks, and corrects boundary and
coefficient-ring assumptions. Detailed statements, proofs, and declaration
names belong in the TeX exposition. The status file tracks the still-open
analytic and combinatorial interpretation work without maintaining a second
claim register.

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

## Inherited focused-validation receipts

These are receipts from their named source checkpoints, not a fresh aggregate
build of the current merged corpus. The campaign status preserves the pinned
merge and validation history.

| Source surface | Recorded receipt and scope |
| --- | --- |
| `AppellSequence` | Eleven public lemmas passed direct sequential compilation; the caller refactor in `FinitePrefixThueMorseCollapse` also passed its own direct check. |
| `StirlingCompleteHomogeneous` | Eight public theorems passed focused compilation. The campaign's duplicate second-kind evaluation formulas were removed in favor of this shared API. |
| `ExponentialRescaling` | Four public lemmas passed focused compilation; existing `NorlundDiagonal` helper names were retained through the shared API. |
| `AbelPolynomialSeries` | A focused source build passed. Coverage of the entire canonical Abel statement remains subject to its current claim audit. |
| `GridEvaluationCertificate`, `IntegerCRTCertificate` | Nine public theorems compiled with the standard project axiom set; their human statements and proofs are grouped in the manuscript's two certificate theorems. |
| `BernoulliFormalLog`, `NorlundGeneralized` extensions | Source/API reviews were recorded; their compilation and affected-dependent closure remain separate outstanding work. |

The moment-cumulant crosswalk retains its normalization and degree boundaries.
The second-kind Stirling set-partition cardinality bridge is established;
weighted per-profile interpretations, surjections, cycles, and descents retain
their separate formalization obligations.
The Nörlund and Bernoulli discussions distinguish formal coefficient algebra,
coefficient-ring transport, multiplicity interpretations, and analytic
convergence. The certificate discussion distinguishes deterministic
certificates from probabilistic testing. These boundaries are maintained in
the exposition and must be preserved through later coverage upgrades.
The following source-review notes add the latest reusable-series detail without
changing the receipt classifications above.

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
