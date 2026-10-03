# Source audit and claim boundaries

Audit date: 2 October 2026.

## Repository

Repository: https://github.com/VladimirReshetnikov/ProveIt

Frozen commit: `44983ed7ebfd545de55bfdb50e040c82f3d24295`.

The snapshot was obtained from the GitHub tree API. Relevant reads included the
Computability directory and the HilbertTenthProblem README and Papers index.
The principal scope source was:

https://github.com/VladimirReshetnikov/ProveIt/blob/44983ed7ebfd545de55bfdb50e040c82f3d24295/Computability/HilbertTenthProblem/README.md

The README describes many computational-substrate reports and distinguishes
complete unbounded-time compilers from finite-horizon reductions. Its reported
75-operation complete certificate and 87-operation universal-polynomial bounds
are quoted as repository status. They were not independently reproduced here.
The present package does not change those bounds.

This was a targeted audit, not a proof audit of every repository file or imported
archive. Repository research reports were not treated as automatically proved
merely because they are in the repository.

## Earlier project report

*Linear Quasi-Diophantine Universality: Unique Polynomial Certificates, Boundary
Tests, and an Exact Convex Integrality Gap*, research report prepared for Vladimir
Reshetnikov, 2 October 2026.

The report was located in the user's research Library in PDF and TeX form. The
abstract, source-boundary discussion, boundary-transport definitions, clocked
certificate statement, and typed polynomial split were inspected. Its stated
analytic consequence is a dense nonclosed-range operator, unlike the boundedly
invertible self-adjoint operator constructed in the new article. Its claimed
characteristic-independent binary certificate is not used as a proof dependency.
No prior report is redistributed in this archive.

## Primary literature

1. Yu. V. Matiyasevich, *Enumerable Sets Are Diophantine*, Doklady Akademii Nauk
   SSSR 191(2) (1970), 279–282. Original-paper record:
   https://www.mathnet.ru/dan35274
   Scope: the classical MRDP background and the distinction between a general
   existence theorem and the explicit representation developed here. MRDP is
   not reproved or used in constructing the new path certificate.

2. Andrej Dudenhefner, *Certified Decision Procedures for Two-Counter Machines*,
   FSCD 2022, LIPIcs 228, 16:1–16:18.
   https://doi.org/10.4230/LIPIcs.FSCD.2022.16
   Official PDF:
   https://drops.dagstuhl.de/opus/volltexte/2022/16297/pdf/LIPIcs-FSCD-2022-16.pdf
   Scope: two-counter universality and the importance of the exact instruction
   set. The article's model has arbitrary destinations for increments and both
   test branches. No universality is inferred for a restricted reversible model.
   The PDF was inspected, including the page containing Theorem 6.

3. Charles H. Bennett, *Logical Reversibility of Computation*, IBM Journal of
   Research and Development 17(6) (1973), 525–532.
   https://doi.org/10.1147/rd.176.0525
   Public academic PDF used for reading:
   https://mathweb.ucsd.edu/~sbuss/CourseWeb/Math268_2013W/Bennett_Reversibiity.pdf
   Scope: the antecedent of recording computational history to make transitions
   injective. The branch-digit lift in the new article is proved directly and
   does not invoke thermodynamic conclusions.

4. Peter G. Doyle and J. Laurie Snell, *Random Walks and Electric Networks*,
   Carus Mathematical Monographs 22, MAA, 1984.
   Author-posted version: https://arxiv.org/abs/math/0001057
   Scope: classical electrical-network and random-walk background. The exact
   shunted operator, Green ratios, lifetime bounds, and rationality reductions
   used here are proved directly in the new article.

## Original work and unresolved matters

The manuscript supplies proofs for the guarded affine path lift, coercive
operator, canonical continuant certificate, exact Green dichotomy, Pell descent,
rational-level decision procedure, efficient approximation, lack of a computable
exact cutoff, finite-support quadratic compiler, electrical and killed-walk
interpretations, and characteristic obstruction.

These are presented as a structural synthesis with explicit interfaces. A full
literature-priority search has not been completed. No individually classical
ingredient is claimed as a new discovery, and no named longstanding conjecture
is declared solved.

The local compiler and examples are executable. No numerical universal table,
Lean/Coq formalization, fixed-arity ordinary integer compiler, or physical
halting-detection experiment is included. Further research directions identify
these boundaries rather than silently assuming them away.
