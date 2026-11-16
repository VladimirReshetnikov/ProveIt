# Theorem and artifact ledger

| ID | Statement or artifact | Status |
|---|---|---|
| F1 | Proof-relevant certified-setoid interface composes equality witnesses without deciding equality. | Fully proved in the report; Lean host structure supplied; object proof pending. |
| A1 | Ideal-combination witnesses present `Z[x]/(g_1,...,g_r)` exactly as a certified setoid. | Fully proved in the report; Python certificate checker supplied; object proof pending. |
| A2 | Localization equality by a killing exponent is an equivalence relation and a ring congruence. | Fully proved algebraically; detailed exponent formulas supplied; Lean target supplied. |
| Z1 | Power-cover lemma: from `sum c_i f_i=1`, construct `sum d_i f_i^N=1` for every `N>=1`. | Fully proved with explicit primitive-recursive algorithm; Python tested in `Z` and `Z/12`; object proof pending. |
| Z2 | Joint monicity: a module element zero on every principal chart is globally zero. | Fully proved from Z1; object proof pending. |
| Z3 | Principal-cover gluing: compatible fractions in `M_{f_i}` glue by an explicit formula. | Fully proved, including zero divisors and unequal denominators; Python tested; object proof pending. |
| G1 | Certified finite affine atlases give a finitary semantics for a broad class of schemes. | Precise definition and soundness argument supplied; full conventional equivalence theorem left as future work. |
| G2 | Quasi-coherent module data on an atlas are finite localization/descent data. | Fully developed as a certificate interface; general category-theoretic library not formalized. |
| P1 | `P^1` is represented by two affine charts with overlap `R[t,t^{-1}]`. | Fully explicit finite atlas. |
| P2 | `O(d)` on `P^1` has Čech `H^0` free on exponents `0,...,d` for `d>=0`, and zero for `d<0`. | Fully proved by Laurent support separation; Python tested; object proof pending. |
| P3 | `O(d)` on `P^1` has Čech `H^1` free on exponents `d<e<0`; rank `max(-d-1,0)`. | Fully proved with a primitive-recursive normal form; 1,200 randomized exact tests. |
| PN | On `P^n`, mixed-sign monomial summands of the standard Čech complex are contractible; only all-nonnegative and all-negative exponent vectors survive. | Fully proved combinatorially; 240 finite matrix/homotopy cases tested for `n<=6`; full object proof pending. |
| C1 | The standard finite Čech table agrees with conventional `H^q(P^n_R,O(d))`. | Mathematically justified using the standard affine-cover comparison; a complete iPRA formalization of derived-functor sheaf cohomology is not claimed. |
| L1 | Dependency-ordered Lean route to `Prf PRAAx` endpoints. | Detailed outline supplied; no Lean executable was available, so no compilation claim. |
| V1 | Exact Python validation suite. | Eight tests pass; JSON and logs included. |

## Explicit nonclaims

The package does not prove general effective Siegel or Faltings, produce Mordell–Weil quotient representatives, decide equality of arbitrary represented reals, construct exact Puiseux branches from arbitrary Cauchy coefficients, or supply a primitive-recursive universal evaluator for encoded programs.
