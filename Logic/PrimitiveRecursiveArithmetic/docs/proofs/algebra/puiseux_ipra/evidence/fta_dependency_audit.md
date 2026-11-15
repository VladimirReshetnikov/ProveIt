# Audit of the reused FTA one-root proof

Audited file: repo_inspection/FTA_iPRA/FTA_iPRA.tex, central one-root proof and finite-table arithmetization. This is a mathematical review, not Lean compilation or a machine-checked proof certificate.

## Conclusion

No serious gap was found in the central single-root construction. It is suitable as a human-proof dependency for existence of a complex root of a monic polynomial whose algebraic coefficients are evaluated by one fixed primitive-recursive program with finite algebraic codes as numerical parameters. The draft's scope caveat about fixed-degree repeated numerical deflation should be preserved; this audit does not extend it to a uniform arbitrary-degree higher-type composition theorem.

## Checked estimates

* The direction routine avoids FTA: three half-angle square-root constructions put a unit direction within 1/2 of 1; finite binomial powers approximate a kth root. Rational bisection precision t=8 ell+16 gives the stated error, and N=8k+4ell makes the binomial residual at most 2^{-ell}. The final inward scaling ensures |w|<=1.
* The radius search over [-E,E], E=2b+3, brackets the residual norm using bit-size bounds on rational coefficients. Its largest admissible dyadic radius satisfies A/2^n<M(r0)<=A.
* Among 2n+1 decreasing scales there is a three-scale plateau in the maximizing Taylor index. The two geometric tails are each <=V/3. Direction error <=V/16 gives more than the claimed V/4 decrease. Therefore q=1−1/(4D), D=2^n4^{2n^2}, is valid.
* Inverse translation from an apart coefficient yields (r0/U)^i<=C rho^{nj}<=(C rho^j)^i. This establishes the travel bound without taking a variable-degree root.
* The finite product estimate prod(1+x_i)<=1/(1−sum x_i) correctly bounds the auxiliary U_j by R. The block inequality rho^K<=1/2 follows from finite Bernoulli arithmetic.
* The coefficient drift is <=3/(32D)2^{-j}<=B Q^j/(8D), so the residual invariant closes. Position and step invariants are consistent with the previously bounded U_j.
* Sampling at J(t)=K(t+H+2) gives the displayed Cauchy modulus and residual modulus. Every comparison executed by the algorithm is rational; norms are explanatory square-root shorthand backed by squared tests.
* The finite-table formulation keeps the induction predicate quantifier-free. Global Cauchy-name hypotheses are only instantiated at finitely many needed indices. All searches have explicit finite bounds. No universal evaluator for arbitrary PR program codes is used.

## Dependency boundary

To apply the theorem uniformly to exact algebraic coefficient codes, supply one fixed PR evaluator for those codes and its fast-name estimates. Do not feed arbitrary programs into an alleged PR universal evaluator. Exact algebraic candidate enumeration and subsequent finite selection should be proved separately; the FTA theorem supplies root existence, not that exact algebraic backend by itself.
