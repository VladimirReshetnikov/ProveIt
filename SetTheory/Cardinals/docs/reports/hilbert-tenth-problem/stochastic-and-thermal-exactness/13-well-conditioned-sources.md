# Source audit

Repository snapshot: `VladimirReshetnikov/ProveIt`, commit
`44983ed7ebfd545de55bfdb50e040c82f3d24295`, inspected 2 October 2026.

## Directly inspected repository sources

1. Hilbert-tenth-problem README. The pinned opening section reports the
   complete-certificate 75-operation and universal-polynomial 87-operation
   baselines. This work does not change those baselines.
   https://github.com/VladimirReshetnikov/ProveIt/blob/44983ed7ebfd545de55bfdb50e040c82f3d24295/Computability/HilbertTenthProblem/README.md

2. `Diophantine/MRDP.lean`, complete source. Theorems `mrdp`, `mrdp_iff`, and
   `mrdp_dioph_iff` give the existing finite-polynomial interface.
   https://github.com/VladimirReshetnikov/ProveIt/blob/44983ed7ebfd545de55bfdb50e040c82f3d24295/Computability/HilbertTenthProblem/Lean/Diophantine/MRDP.lean

3. `Diophantine/Paper1980/TuringPartrec100.lean`, opening 150 lines.
   Contains the finite-machine construction and begins the `re_tm0` theorem;
   no claim that its entire dependency graph was rebuilt here.
   https://github.com/VladimirReshetnikov/ProveIt/blob/44983ed7ebfd545de55bfdb50e040c82f3d24295/Computability/HilbertTenthProblem/Lean/Diophantine/Paper1980/TuringPartrec100.lean

4. `Diophantine.lean` facade. Used to identify the counter-simulation,
   arithmetic, and MRDP interface paths, not as a substitute for proving
   this manuscript's new theorems.
   https://github.com/VladimirReshetnikov/ProveIt/blob/44983ed7ebfd545de55bfdb50e040c82f3d24295/Computability/HilbertTenthProblem/Lean/Diophantine.lean

Repository access used the GitHub connector. No repository writes were made.
The audit is targeted, not an exhaustive duplication or correctness audit of
all repository content. Current main-branch descriptions were supplemented
with pinned-source reads.

## Earlier supplied research manuscripts

- *Linear Quasi-Diophantine Universality: Unique Polynomial Certificates,
  Boundary Tests, and an Exact Convex Integrality Gap*, 2 October 2026.
  Library TeX source `Linear_Quasi_Diophantine_Universality.tex`.
  Its abstract states the dense nonclosed-range operator result contrasted
  with the boundedly invertible operator here.

- *Arithmetic of Rapidly Mixing Reversible Computation: Diophantine cuts,
  Liouville equilibria, and exact-symbolic barriers*, 30 September 2026.
  Library TeX source `article(20260930-202816).tex`.
  Its abstract records the gapped-chain exact-arithmetic comparison.

These manuscripts were retrieved from the user's Library and are cited as
research antecedents, not peer-reviewed or independently formalized results.
The new proofs do not require importing their conclusions.

## Classical primary-source antecedents

- Charles H. Bennett, *Logical Reversibility of Computation*, IBM Journal of
  Research and Development 17(6), 525–532 (1973).
  DOI: https://doi.org/10.1147/rd.176.0525
  Original article text and first-page image inspected at:
  https://mathweb.ucsd.edu/~sbuss/CourseWeb/Math268_2013W/Bennett_Reversibiity.pdf

- Stephen Demko, William F. Moss, Philip W. Smith, *Decay rates for inverses
  of band matrices*, Mathematics of Computation 43(168), 491–499 (1984).
  DOI: https://doi.org/10.1090/S0025-5718-1984-0758197-9
  AMS bibliographic result consulted. No unproved decay estimate from this
  paper is imported; the manuscript proves its Neumann bound directly.

## Novelty and trust qualification

Searches for compact-support undecidability and resistor-network variants
were inconclusive as a priority audit. No absence-of-prior-literature claim
is based on those searches. The combined connected coercive compiler, exact
Lucas charge law, finite-prime bound, and specified sparsity threshold are
presented with complete proofs as candidate structural research contributions.
They have not been independently refereed or kernel-checked.
