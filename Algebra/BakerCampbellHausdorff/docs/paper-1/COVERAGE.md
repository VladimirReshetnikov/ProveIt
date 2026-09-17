# Coverage guide

The detailed formula-by-formula coverage table is **Appendix D** of the paper.
This file provides a short navigation map. Scope is the English Wikipedia
BCH page, revision 1368909113, consulted 16 September 2026.

| Paper section | Mathematical content covered |
|---|---|
| 1 | Formal, local analytic, and global interpretations; notation and scope |
| 2 | Exp/log inverses; full associative expansion; finite formula for every word; multiple factors |
| 3 | Coproduct, antipode, grouplikes, primitives, Dynkin–Specht–Wever, Friedrichs, full Dynkin formula, free Lie algebra and enveloping algebra |
| 4 | Campbell–Hadamard identity, conjugation and braiding, differential of exp, Bernoulli coefficients |
| 5 | BCH differential equations, Poincaré integral, all powers of Y, independent homogeneous recursion |
| 6 | Every displayed BCH term through degree 6; associative terms through degree 4; swap/reversal symmetry and associativity |
| 7 | Both elementary norm bounds, quantitative remainder, trace branches, all logarithms of the page's matrix example and proof of BCH divergence |
| 8 | Matrix and intrinsic Lie-group meanings, local exponential coordinates, local correspondence, integration, nilpotent polynomial groups |
| 9 | Commuting and central-commutator cases; exact eigenvector resummation, braiding, resonance and convergence distinctions |
| 10 | All Zassenhaus exponents, displayed C2–C4, three recurrences, finite weighted-tree formula, convergence |
| 11 | Trotter limit, symmetric second order, Suzuki's arbitrary even order, complete local logarithmic error series |
| 12 | All infinitesimal and structure-constant formulas; correct coframe; pullbacks; Killing form; every metric coefficient; rotation-algebra example |
| 13 | Position–momentum identities, Weyl relations, domain counterexample, creation/annihilation, normal ordering, displacement composition, all oscillator matrix elements |
| A | Elementary PBW proof; Hopf structure on any enveloping algebra; counterexample showing why coproduct completion is needed |
| B | Complete degree-5 and degree-6 associative coefficient certificates |
| C | Reproduction instructions and exact-check scope |
| D | Formula-by-formula coverage and corrections index |

## Assertions requiring correction or explicit hypotheses

- The usual algebraic tensor product is too small for general infinite-series
  coproducts; use the degree-completed tensor product.
- Grouplike elements are normalized by counit/constant term 1; zero is not
  a group element merely because it satisfies Delta(0) = 0 tensor 0.
- The page's matrix M represents ad_X, not the vielbein. W is the coframe
  matrix; its inverse is the dual frame. In a positive-dimensional Lie
  algebra, M is always singular.
- `(I-exp(-M))/M` denotes a removable analytic matrix function, not an
  actual inverse of M.
- Pullbacks require Jacobian factors for a general map. A Killing form or
  its pullback need not be a nondegenerate metric.
- The trace identity concerns the BCH branch and is not valid for arbitrary
  choices of logarithm.
- Smallness is a sufficient general convergence condition, not a necessary
  condition for every special pair or for every resummed exponential identity.
- The eigenvalue 0 in s/(1-exp(-s)) is removable; nonzero 2*pi*i integers
  are genuine resonances. Resummed validity does not imply Taylor convergence.
- The alternate Zassenhaus product starting at n=1 needs C_1=Y.
- Unbounded-operator identities require an appropriate representation and
  domains; a bare dense-domain CCR does not imply the Weyl relations.

Historical attributions and usage claims are not propositions requiring
mathematical proof. Theorems merely listed as links, such as Stone–von Neumann
and Golden–Thompson, are outside the stated scope; the page's actual quantum
exponential formulas are proved directly.
