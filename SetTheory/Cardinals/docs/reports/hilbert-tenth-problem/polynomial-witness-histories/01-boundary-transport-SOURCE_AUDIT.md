# Source audit and claim boundaries

Audit date: 2 October 2026.

## Repository baseline

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `48ee077c7ab647d7121370e95a353169c89c79db`.
Commit timestamp: `2026-10-02T19:11:29Z`.

The GitHub connector was used to read repository metadata, the Computability
and HilbertTenthProblem structure, the Hilbert-tenth-problem overview and
research summaries, and the MRDP-to-Dioph source bridge. The following paths
are the primary comparison points:

1. `Computability/HilbertTenthProblem/README.md`: distinguishes established
   75-operation complete-certificate / 87-operation universal-polynomial bounds
   from horizon-dependent substrate certificates and other compiler metrics.
2. `Computability/HilbertTenthProblem/Lean/Diophantine/Common/RecursivelyEnumerableDioph.lean`:
   contains `rePred_dioph`, using `MRDP.mrdp` and the finite-polynomial interface.
3. `Computability/HilbertTenthProblem/Papers/`: research-paper organization and
   links to the native-stream-queue research summaries.

This is a focused audit, not an exhaustive review of every imported research
archive, source file, or formal proof. The full repository was not built.
Repository source comments and overview claims are attributed to the repository;
they are not reported as having been independently rechecked by the Lean kernel.

## External primary sources

- Andrej Dudenhefner, *Certified Decision Procedures for Two-Counter Machines*,
  FSCD 2022, LIPIcs 228, 16:1–16:18.
  https://doi.org/10.4230/LIPIcs.FSCD.2022.16
  Used for the universality/undecidability premise and the warning that counter
  instruction conventions matter. The article's machine has arbitrary branch
  destinations and contains the CM2 convention described in the source.
- Marvin Minsky, *Computation: Finite and Infinite Machines*, 1967.
  Classical background, also cited in Dudenhefner. No claim to have audited an
  entire copy of this book during the present task.
- Paliath Narendran, *Solving linear equations over polynomial semirings*,
  LICS 1996, 466–472.
  https://lics.siglog.org/archive/1996/Narendran-Solvinglinearequati.html
  Precedent for undecidability of linear polynomial equations with nonnegative
  coefficient restrictions; the official conference abstract was consulted.
- Ruiwen Dong, *Solving Homogeneous Linear Equations over Polynomial Semirings*,
  STACS 2023, LIPIcs 254, 26:1–26:19.
  https://doi.org/10.4230/LIPIcs.STACS.2023.26
  Contrast: a particular single homogeneous univariate equation with every
  unknown polynomial nonzero and nonnegative has a polynomial-time decision
  procedure. This does not cover the mixed-subring equations here.
- Ruiwen Dong, *Linear equations with monomial constraints and decision problems
  in abelian-by-cyclic groups*, SODA 2025, 1892–1908.
  https://doi.org/10.1137/1.9781611978322.59
  https://arxiv.org/abs/2406.08480
  Precedent for undecidability with designated monomial unknowns over a Laurent
  polynomial ring; those restrictions differ from this report's subring sorts.
- Yuri Matiyasevich, *Towards finite-fold Diophantine representations*,
  Journal of Mathematical Sciences 171 (2010), 745–752.
  https://doi.org/10.1007/s10958-010-0179-4
- D. Cantone, L. Cuzziol, E. G. Omodeo, *On diophantine singlefold specifications*,
  Le Matematiche 79(2) (2024).
  https://lematematiche.dmi.unict.it/index.php/lematematiche/article/view/2703
  The latter two sources clarify why uniqueness of a polynomial-valued
  certificate is not the ordinary integer single-fold question.

## What this report establishes internally

The report supplies written proofs of the complete finite-support transport
fiber, the clocked unique-history theorem, boundary splitting, the sparse
compiler, scalar row tagging, the integer-versus-real energy gap, exact Hilbert
range membership, and the restricted one-counter decision algorithm. It supplies
executable exact tests for the compiler and the principal finite identities.

It does not claim that the generic incidence or geometric-series ingredients are
new. It does not establish first publication priority for the combined normal
form or solve a separately documented classical open conjecture. The research
contribution presented is an explicit theorem package, compiler, and set of
precisely delimited follow-up questions for the ProveIt program.

## Reproducibility boundaries

A halting runtime bound of 32 is used only in finite test enumeration. It is
not a bound in the mathematical compiler. The final validation report records
32,502 exact checks. A universal numerical transition table is not instantiated,
and no new Lean files are included. No source PDFs or font files are redistributed.
