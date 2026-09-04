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
[`PROVENANCE.md`](Combinatorial_Coefficient_Calculus/PROVENANCE.md), the live
and historical hashes in
[`SOURCE_CLOSURE.sha256`](Combinatorial_Coefficient_Calculus/SOURCE_CLOSURE.sha256),
and the topic/claim decisions in
[`SOURCE_DISPOSITION.csv`](Combinatorial_Coefficient_Calculus/SOURCE_DISPOSITION.csv).
The standard-library
[`validate_canonical.py`](Combinatorial_Coefficient_Calculus/validate_canonical.py)
checks LaTeX structure, labels, references, citations, proof pairing, source
coverage, and the one-publication layout. Run it with `--final` at a
synchronized publication checkpoint. The current source is structurally
complete, but its closure row and publication PDF still await refresh.

| Directory | Document |
| --- | --- |
| `Combinatorial_Coefficient_Calculus/` | **Canonical:** *Combinatorial Coefficient Calculus* — current 10,391-line, 504,431-byte source; the retained 174-page A4 PDF belongs to the preceding synchronized checkpoint |

The preceding publication receipt paired an 8,966-line, 390,732-byte source
with the retained 174-page PDF in one clean three-pass `pdflatex` run. The
canonical TeX has since advanced, so that receipt is historical and no render
parity is asserted for the current source until a new PDF is built and the
purpose-specific closure is refreshed.

## Current formalization checkpoint

The in-document register covers 201 theorem-like or algorithm items: 59 are
classified Lean, 35 partial, and 107 none. Its 201 adjacent proof environments
remain a structural property, separate from those formalization statuses.

Recent crosswalk work closes the full Cauchy-polynomial theorem block: the
formal and real interval integrals, reflection, and generic generating-function
and addition laws are now represented, with the latter two valid after
evaluation in any commutative rational algebra. The analytic convergence and
branch assertion attached to the generating function remains outside that
formalized theorem block. The second-kind reverse-row recurrence is now
machine checked in a division-free integral form, including its zero boundary
case beyond the range used by the displayed human formula. The ordinary versus
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

## What this package does not claim

The manuscript is research-frontier mathematical writing. Its theorem and proof
environments are human-readable mathematics, not evidence of Lean verification.
The section "Lean formalization register" states, per result, what is formalized
and what is not; it is maintained separately from this consolidation.
