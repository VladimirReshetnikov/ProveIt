# Sources, provenance, and verification boundaries

Prepared September 30, 2026. Full bibliographical details also appear in the
article. This file distinguishes the external inputs from the constructions
and finite checks developed in this package.

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Immutable commit inspected:
`e18718e837d43e162252f9a314e8cb797fbd1a1f`.

Relevant documents read through the GitHub connector:

1. `Computability/HilbertTenthProblem/README.md`
2. `Computability/HilbertTenthProblem/Lean/MRDP.md`

The MRDP guide states the fixed finite-polynomial natural-number interface,
its converse, the treatment of zero, and the distinction between an existence
theorem and a practical polynomial-generation algorithm. These are the points
used here. Repository statements about axiom audits and successful builds are
reported as documented status, not independently reproduced checks.

The report does not assert that every article in the repository was inspected.
No repository files were edited or uploaded.

## Primary mathematical sources and their roles

**David Harel (1986).** “Effective transformations on infinite trees, with
applications to high undecidability, dominoes, and fairness.” Journal of the
ACM 33(1), 224–248. DOI: 10.1145/4904.4993.

Role: classical high-undecidability provenance. The counter-machine recurrence
statement was corroborated in the modern primary source below, rather than
reconstructed from a publisher abstract alone.

**Miroslav Chodil and Antonín Kučera (2025).** “The Satisfiability and Validity
Problems for Probabilistic Computational Tree Logic Are Highly Undecidable.”
ICALP 2025, LIPIcs 334, 151:1–151:20.
DOI: 10.4230/LIPIcs.ICALP.2025.151.
Full version: https://arxiv.org/abs/2504.19207

Role: Appendix A explicitly records Sigma^1_1-completeness of recurrent
reachability for nondeterministic two-counter Minsky machines and attributes
the classical result to Harel. This package does not claim their PCTL results
or rely on unverified details of that PCTL encoding.

**Douglas Cenzer, Victor W. Marek, Jeffrey B. Remmel (2013 arXiv version).**
“Index sets for Finite Normal Predicate Logic Programs.”
https://arxiv.org/abs/1303.6555

Role: effective primitive-recursive-tree indexing and standard index-set
background. In particular, Theorem 2.6(g) states analytic completeness of
nonempty path spaces; Theorem 2.10(e) states Sigma^0_3-completeness of existence
of a recursive path. The report proves the corresponding recurrence and
deadline classifications directly, rather than treating the underlying
index-set phenomena as novel. The source's specialized use of “decidable
tree” should not be confused with decidable membership in a tree.

**Cristopher Moore (1991).** “Generalized shifts: unpredictability and
undecidability in dynamical systems.” Nonlinearity 4(2), 199–230.
DOI: 10.1088/0951-7715/4/2/002.
Author publication list: https://sites.santafe.edu/~moore/pubs.html

Role: historical context for computational dynamics. The planar stack formulas
in this package are proved directly and do not require importing an unstated
geometric theorem from Moore's paper.

**Anthony Widjaja To and Leonid Libkin (2008).** “Recurrent Reachability Analysis
in Regular Model Checking.” LPAR 2008, LNCS 5330, 198–213.
DOI: 10.1007/978-3-540-89439-1_15.
Author-hosted text: https://homepages.inf.ed.ac.uk/libkin/papers/lpar08b.pdf

Role: contrast with restricted infinite-state classes admitting decidable
recurrent reachability. Used in the future-research discussion, not as a
premise for this package's undecidability proofs.

## What was established in this package

The article supplies the algebraic proofs of the incoming-edge compiler and
coefficient bound, compatible deadline compactness and certificate formulas,
explicit witness-separation constructions, and the exact planar stack formulas.
It identifies the classical normal-form and universality inputs to the
fixed-law completeness theorem.

The Python code independently implements machine successors, expanded sparse
integer polynomials, residual evaluation, finite deadline exploration, and
exact rational stack operations. Finite checks passed; they do not decide or
validate arbitrary infinite behavior.

No full universal machine instruction table was instantiated, no theorem
prover checked the new proofs, and no comprehensive priority search has been
completed. A source code inspection, an exact regression test, a conventional
mathematical proof, and a proof-assistant audit are different forms of evidence.
