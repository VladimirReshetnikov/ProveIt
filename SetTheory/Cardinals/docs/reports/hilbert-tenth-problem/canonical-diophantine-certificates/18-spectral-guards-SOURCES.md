# Source audit and provenance

Research date: 2 October 2026.

## Repository inspection

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected fixed tree commit:
`e58b724c25bd34533b7a5834cfcbe873dfa01288`

The GitHub connector was used to inspect repository trees and retrieve:

1. `Computability/HilbertTenthProblem/Lean/Diophantine/Common/DiophantineTrace.lean`
   (complete retrieved source; blob
   `08e5796b22fc85ef0cd97255dba8b7527960160b`).
   It provides `boundedForall_dioph`, `exactIter_dioph`, and
   `existsExactIter_dioph`, proving ordinary Diophantine closure contracts.
   This was not construed as a proof of single-foldness or of this manuscript.

2. `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/README.md`
   (opening report overview, manuscript table, and contribution summaries).
   Used to identify existing polynomial-trajectory, pumping, causal,
   memory, routing, and related reports and avoid merely repeating a generic
   tableau compiler. The comparison with the polynomial-trajectory component
   is based on this report description, not an independent full audit of its
   million-byte merged TeX manuscript.

3. The same directory's `02-poly-trajectories-sources.md` (complete retrieved
   source). Used to identify the predecessor's literature and its stated
   formalization/novelty boundaries.

The root README was also consulted for general project context. The repository
was not rebuilt, comprehensively axiom-audited, or exhaustively searched for
all possible overlapping constructions. The manuscript pin is a source
snapshot, not a claim that all repository content is mathematically verified.

## Primary literature

- D. Larchey-Wendling and Y. Forster, *Hilbert's Tenth Problem in Coq
  (Extended Version)*, LMCS 18(1), article 35 (2022).
  https://arxiv.org/abs/2003.04604
  https://doi.org/10.46298/lmcs-18(1:35)2022
  Abstract and bibliographic record consulted. Used for the established
  MRDP/counter-machine/FRACTRAN formalization landscape.

- M. Hark, F. Frohn, J. Giesl, *Termination of Triangular Polynomial Loops*,
  arXiv:1910.11588v7 (2024).
  https://arxiv.org/abs/1910.11588
  Abstract and version metadata consulted. Used to distinguish established
  closed-form termination analysis from the certificate-size and uniqueness
  question studied here.

- F. Frohn, J. Giesl, P. Giesl, N. Lommen, *On Deciding Constant Runtime of
  Linear Loops*, arXiv:2601.08492 (2026).
  https://arxiv.org/abs/2601.08492
  Abstract and bibliographic record consulted. Real-eigenvalue constant-runtime
  results concern a different question; the manuscript does not claim priority
  for decidability of linear-loop termination.

- D. Cantone, L. Cuzziol, E. G. Omodeo, *On diophantine singlefold
  specifications*, Le Matematiche 79(2), 585-620 (2024).
  https://doi.org/10.4418/2024.79.2.18
  https://arts.units.it/bitstream/11368/3101478/1/CCO24.pdf
  Journal metadata and deposited PDF consulted; printed page 590 visually
  inspected. Used for classical single-fold exponential representations and
  the danger of nonunique auxiliaries under naive disjunction/gating.

- Yu. V. Matiyasevich, *Towards finite-fold Diophantine representations*,
  Journal of Mathematical Sciences 171, 745-752 (2010).
  https://doi.org/10.1007/s10958-010-0179-4
  Publisher bibliographic record consulted for finite-fold context.

- P. Bacik, T. Karimov, F. Luca, J. Nieuwveld, J. Ouaknine, D. Purser,
  J. Worrell, *A survey of the Skolem and Positivity Problems for linear
  recurrence sequences*, submitted, 2026, 59 pages.
  https://people.mpi-sws.org/~joel/publications/skolem_and_positivity_survey26abs.html
  Author-hosted abstract and bibliographic record consulted. Used for the
  current general-problem boundary, not to assert novelty of the present
  restricted construction.

Additional searches covered real-spectrum positivity and Chebyshev systems.
No historical-priority conclusion was drawn from the absence of a search hit.
The real-zero bound is a classical mechanism and is reproved in full in the
article. The explicit endpoint compiler, its gate counts, tail bound, and
worked examples have self-contained proofs rather than being inferred from
abstracts.

## What is new in the supplied work, and what is not asserted

The work develops and tests a particular canonical root-removing sign-chart
construction for integer positive-root polynomial-exponential sequences. Its
relation to the inspected ProveIt polynomial-trajectory construction is an
explicit extension of the spectral class and arithmetic certificate design.
This is not a claim to have discovered recurrence positivity decidability,
single-fold exponential Diophantine representability, the sum-of-squares
quartic reduction, or binary powering.

No proof assistant checked the manuscript. The Python tests are exact finite
checks, not substitutes for mathematical proof. Matrix/Jordan and global
certificate composition are article-level results, not implemented frontends.
