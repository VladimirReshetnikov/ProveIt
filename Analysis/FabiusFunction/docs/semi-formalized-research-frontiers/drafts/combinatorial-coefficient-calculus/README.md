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
| `Combinatorial_Coefficient_Calculus/` | **Canonical:** *Combinatorial Coefficient Calculus* — the evolving source and a historical 174-page A4 PDF |

The TeX has changed since the committed PDF was rendered. PDF rebuilding is
currently skipped at the user's request, so the pair has no current
render-parity claim. Standalone checksum files are retired; provenance is kept
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

The combined register contains 204 rows.  The retained formal-power result and
the ordinary-composition multiplicity theorem below each promote one previously
partial row; the Abel, Raney, and associahedron sources also replace five
previously empty rows with one exact and four partial crosswalks.  The live
totals are therefore **62 Lean, 36 partial, and 106 none**.
Earlier classifications are inherited; these counts are a coverage register,
not a fresh rebuild of every proof. Structural/provenance validation checks 204
adjacent proofs, 27 disposition records, and six original-source inventory
rows; the current source pass sees 706 labels and zero missing Lean declaration
names. PDF rebuilding remains deferred at the user's request.

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
logarithm calculation in the Nörlund proof, but it does not construct
arbitrary-order Nörlund polynomials and therefore does not promote that row.

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
Arbitrary-order Nörlund polynomials and their analytic convergence remain open
formalization work.

## Ordinary composition multiplicities (2026-09-04)

`OrdinaryBellMultinomial` gives a finite profile set for the multiplicities of
parts of sizes `1,…,n`, characterizes its two constraints, and proves the
multinomial formula for ordinary partial Bell polynomials over every
commutative semiring. Its composition corollary works over every commutative
ring and includes degree zero: the unique empty profile gives `c₀=a₀`.
Together with the upstream finite-degree locality theorem
`ordPartialBell_congr_of_le`, these are five new public declarations. The live
source census is therefore 976 modules and 12,116 explicit declarations.

Direct sequential Lean checks passed for all nine new or changed modules in
this merge, the three ordinary-composition callers, and the complete facade
import check against the compiled dependency cache. The Raney proof was
repaired before this check; its derivative, scalar-coefficient extraction,
and nonzero-factor cancellation now elaborate. This is a focused validation,
not a fresh build of the whole corpus. The canonical validator passes with
zero errors or warnings, and crosswalk regeneration applies no pending remarks.
