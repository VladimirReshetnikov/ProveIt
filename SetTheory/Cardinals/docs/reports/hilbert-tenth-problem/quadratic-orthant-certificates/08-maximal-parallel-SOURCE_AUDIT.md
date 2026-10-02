# Source audit

Access date: 2 October 2026. The search was targeted, not exhaustive.

## Repository

Repository: https://github.com/VladimirReshetnikov/ProveIt

The recursive tree response reported:
`db3b377f0ae3ab8cb585df4eb4b859cbee5ba3c5`.

The following source was fetched again explicitly at that commit:
`Computability/HilbertTenthProblem/Lean/Diophantine/MRDP.lean`.
Its blob SHA was `74aea8c5e75923c7f8b0c041388b91e10e729d65`.
This file supplies the finite-polynomial `Diophantine.mrdp` interface.
It was inspected, not rebuilt in this session.

The live-branch catalogue consulted was:
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/README.md`.
It describes prior work on Petri traces, priority arithmetic and reactions,
queues, heaps, self-assembly, and routing. In particular it already records
the low-degree orthant-positive semilinearity classification and single-fold
quadratic semilinear representations. These are credited rather than claimed
as new. The full merged report and all formal developments were not audited.

Some repository search results carried older indexed revision
`4cccfa06866b6b81b2467e1cf7514ea85ed0216d`; they were used for navigation,
not to assert a complete snapshot rebuild or consistency of all snippets.

## External primary literature

1. Artiom Alhazov and Sergey Verlan, *Minimization Strategies for Maximally
   Parallel Multiset Rewriting Systems*, TCS 412 (2011), 1581–1591;
   author preprint https://arxiv.org/abs/1009.2706.
   Used for established universality and the published 23-rule example.
   The accessible abstract was inspected; the full rule table was not
   reproduced or compiled. No claim of current minimality is made.

2. Linqiang Pan, Gheorghe Păun and Bosheng Song, *Flat maximal parallelism
   in P systems with promoters*, TCS 623 (2016), 83–91;
   https://doi.org/10.1016/j.tcs.2015.10.027.
   Used for the established flat-maximal semantic variant. Historical open
   questions in that paper are not described as still open in 2026.

3. Kevin Woods, *Presburger arithmetic, rational generating functions, and
   quasi-polynomials*, JSL 80 (2015), 433–449;
   https://arxiv.org/html/1211.0020v2.
   Used for finite-fiber Presburger counting and eventual quasipolynomiality.
   The resource-cover exponent and its sharpness are proved in this manuscript.

4. Leslie G. Valiant, *The complexity of enumeration and reliability problems*,
   SIAM J. Comput. 8 (1979), 410–421;
   https://doi.org/10.1137/0208032.
   Original PDF inspected at
   https://www.math.cmu.edu/~af1p/Teaching/MCC17/Papers/enumerate.pdf.
   PDF pages 1 and 5 (printed pages 410 and 414) were visually inspected.
   The paper's reductions are oracle/Turing reductions. This distinction is
   preserved in the article's #P statement.

5. Marvin L. Minsky, *Computation: Finite and Infinite Machines*, Prentice-Hall,
   1967. Classical register-machine background. The elementary operational
   embedding used in this article is proved directly; the book was not
   reproduced or re-audited here.

## Novelty and verification boundaries

The article provides proofs for its explicit compiler, quantitative bounds,
sharpness constructions and convexity obstruction. It does not establish a
verified first occurrence in the entire literature. It does not certify a
solution to a named long-standing conjecture, a universal-rule minimality
question, or a general finite-fold/single-fold problem. Executable finite tests
check the implementation and examples; conventional proofs support the
universal mathematical assertions.
