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
[`PROVENANCE.md`](Combinatorial_Coefficient_Calculus/PROVENANCE.md), the
historical publication and intake digests in
[`SOURCE_CLOSURE.sha256`](Combinatorial_Coefficient_Calculus/SOURCE_CLOSURE.sha256),
and the topic/claim decisions in
[`SOURCE_DISPOSITION.csv`](Combinatorial_Coefficient_Calculus/SOURCE_DISPOSITION.csv).
The standard-library
[`validate_canonical.py`](Combinatorial_Coefficient_Calculus/validate_canonical.py)
checks LaTeX structure, labels, references, citations, proof pairing, source
coverage, the digest closure, and the one-publication layout.  Its `--final`
mode passed at the last PDF publication checkpoint.  It is not a current-pass
claim after the crosswalk-only TeX update, because the intentionally historical
closure digest is expected to differ until the next PDF publication cycle.

| Directory | Document |
| --- | --- |
| `Combinatorial_Coefficient_Calculus/` | **Canonical source:** *Combinatorial Coefficient Calculus* — 10,356-line, 499,570-byte live TeX; the retained 174-page A4 PDF is a historical, unrebuilt artifact |

The retained PDF rendered the TeX at the package's last three-pass
`pdflatex` publication checkpoint.  The live TeX has since acquired the
2026-09-04 Lean crosswalk and regenerated formalization register, while the PDF
was deliberately not rebuilt.  The PDF is therefore historical: **no render-
parity claim applies to the current TeX/PDF pair**, and the TeX is the
authoritative live source.

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
environments are human-readable mathematics, not by themselves evidence of Lean
verification.  The generated section "Lean formalization register" states, per
result, what is formalized and what is not: its current 201 rows comprise 56
Lean, 34 partial, and 111 none.  The 2026-09-04 crosswalk connects the Bell
normalization and unit-series coefficient formulas to the 0-definition,
16-theorem module `UnitSeriesBellCoefficients`; it expressly leaves the
labelled-set partition interpretation unformalized.
