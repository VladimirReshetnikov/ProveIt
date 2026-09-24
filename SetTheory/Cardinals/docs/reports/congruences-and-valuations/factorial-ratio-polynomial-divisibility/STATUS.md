# Research-status and verification notes

Date of source check: September 19, 2026.

## Selected conjectures

The following live source entries were inspected:

- https://oeis.org/A211417
- https://oeis.org/A295431

Both entries contain Peter Bala's August 28, 2025 uniform-divisibility questions.
At the time of inspection the general product-length statements remained
conjectural in those entries. A211417 separately records a June 30, 2026 proof
of divisibility by `30*n-1`. That special case is also listed in Appendix A of:

Tom Adamczewski, *OEIS Open: How many conjectures can language models turn into
theorems?*, arXiv:2608.11941 (August 2026),
https://arxiv.org/abs/2608.11941.

That previously proved single-factor result is not claimed as new here. The
selected target is the all-product-length phenomenon and its structural
explanation. Unrelated conjectures in these OEIS entries, such as those on
supercongruences or gamma-interpolated values, are not claimed to be settled.

## Results offered by this manuscript

Theorem 3.1 supplies a necessary-and-sufficient criterion for a polynomial that
splits over the rationals to divide a balanced integral factorial-ratio sequence
up to one fixed integer multiplier. It gives a constructive bound. Its proof
uses factorial valuations, one-sided step-function values, and Dirichlet's
theorem on primes in arithmetic progressions for the necessity direction.

Theorem 4.1 reduces the criterion at height one to a sign test on divisibility
counts of factorial parameters. Section 5 applies the criterion to the two
selected OEIS sequences and proves explicit multipliers for arbitrary product
length. Section 6 gives computer-assisted proofs that the eight proposed
particular multipliers are least possible, using finite digit graphs.

All of these are proof claims made and justified in the attached manuscript.
They have not been independently peer reviewed or formalized in Lean. The
source search does not establish that every equivalent formulation of the
classification theorem is absent from the existing literature. A statement
remaining conjectural in an OEIS entry is evidence of the entry's recorded
status, not an exhaustive worldwide publication-priority certificate.

## Computation versus proof

The conventional proofs establish the all-index existence, obstruction,
classification, and product-family claims without extrapolating from a finite
sample. The 60 finite certificates establish the remaining small-prime bounds
for the eight optimal constants. A separate verifier checked 1,685 states and
19,277 exact integer transition inequalities, as well as equality witnesses
and complete prime coverage. Larger primes are handled by the proved cutoff,
not by sampling them.

Regression tests are an additional error-detection layer only. Their saved
record is `data/test_results.json`. The recurrence and displayed rational
asymptotic coefficients were checked exactly as well. No floating-point
calculation is used as an integrality proof.

## Reproducibility and presentation

The delivered PDF was compiled with pdfLaTeX, rendered, and visually inspected.
Its final length is 20 pages. The archive contains the exact source, the atlas
input required to compile it, all certificate data, a separate checker, and
regression tests. No background task, remote computation, or unavailable
service is needed to reproduce the checks.
