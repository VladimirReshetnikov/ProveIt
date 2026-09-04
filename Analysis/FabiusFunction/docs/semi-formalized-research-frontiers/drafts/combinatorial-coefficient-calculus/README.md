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

The `AppellSequence` extension has passed a focused Lean build with
`LAKE_JOBS=1`: eleven public lemmas provide weighted binomial translation,
convolution transport, cancellation, and inversion. The manuscript gives their
complete human proofs and exact declaration crosswalks. Three private rational
helpers in `FinitePrefixThueMorseCollapse` were replaced by the shared API; that
caller refactor has been independently source-reviewed but awaits its own build.

The register contains 205 rows: 59 marked Lean, 34 partial, and 112 without a
Lean counterpart. The earlier classifications are inherited; this checkpoint
adds three compiler-backed entries and does not claim a fresh build of the whole
corpus. The final structural/provenance validator passes with 205 adjacent
proofs, 27 disposition records, and six original-source inventory rows. PDF
rebuilding remains deferred at the user's request.

The same-day upstream crosswalk connects the Bell normalization and unit-series
coefficient formulas to `UnitSeriesBellCoefficients`; its labelled-set partition
interpretation remains unformalized. That partial result is included in the
register totals above.

`ExponentialRescaling` has passed a focused build. Its four public lemmas give
the rescaling chain rule over every commutative semiring and exponential
specializations over every commutative rational algebra. They replace the
rational-only helpers in `NorlundDiagonal` without changing their names. The
manuscript supplies full coefficient proofs and an exact crosswalk.

The pending `AbelPolynomialSeries` source constructs a solution over every
commutative rational algebra, derives coefficients for every solution, and
proves the full EGF and binomial identity including degree zero. The new
`BernoulliFormalLog` source derives the rational formal logarithm of the
Bernoulli kernel using the existing recurrence-to-logarithm bridge. Its
coefficient formula separates degree zero and preserves the distinction between
the two degree-one Bernoulli conventions. These two modules and the affected
Norlund, Lambert, and ThueMorse callers still await compilation; independent
source reviews are not compiler validation, and their register classifications
have not been promoted on that basis.

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
