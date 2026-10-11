# Source audit

## Fixed baseline

Repository: https://github.com/VladimirReshetnikov/ProveIt

Revision: `7bd45777a8a127e5dc69aff8887ca36a79a3059d`

Commit: `New research reports`, 2026-10-11 01:57:13 UTC.

The source comparison examined the requested manuscript and incoming directory, relevant earlier continuations, and all eleven incoming research archives at this revision. The source hash manifest records the exact files. This was a targeted review for overlap, proof dependencies, and concrete research questions, not a complete certification of every repository theorem.

## Relevant dependencies

- The cubic harmonic report provides the immediate contour strategy, its proved cubic finite-part identity, and its explicitly requested quartic case.
- The harmonic-parity report supplies the centered parity criterion, the trigamma-square baseline, and the rational resolvent generator. Its Questions R1 and R4 are the direct targets.
- The ordered-Hurwitz report fixes strict-depth and harmonic Laurent conventions.
- The higher-reflection report treats fourth Tornheim ray derivatives, which are distinct from the fourth digamma power treated here.
- The exact-resonant report already proves the complete convergent Cayley shuffle ideal obstruction with its specified finite extra relation family.
- The independent-orders report records an unfinished larger modular relation calculation. Its stored checkpoint is not an exhausted search.

## Classical sources checked

The article's external mathematical inputs are cited to primary sources:

1. NIST DLMF Chapters 4, 5, 15, 24, and 25: digamma recurrence/reflection and expansions, Binet integral, Hurwitz Fourier transform, Bernoulli polynomials, regularized Gauss integral, polylogarithm local expansion, and specified Euler sums.
2. D. Borwein, J. M. Borwein, and R. Girgensohn (1995), *Explicit evaluation of Euler sums*, DOI `10.1017/S0013091500019088`: odd-weight double-zeta reduction, with the larger-index-first convention checked against the concrete weight-three and weight-five cases.
3. O. Espinosa and V. H. Moll (2002), *On some integrals involving the Hurwitz zeta function: Part 1*: primary Hurwitz integral context.
4. M.-A. Coppo (2025), *On some remarkable identities related to the harmonic zeta function*: harmonic-Stieltjes conventions and arithmetic context.

Classical methods and named formulas are attributed. Newness is stated relative to the inspected ProveIt corpus, without an exhaustive literature-priority claim.

## Findings

No false theorem was identified in the source formulas used. The appropriate updates are the scoped advances listed in `INTEGRATION.md`.

Two exact normalization issues should be preserved in any extension:

- At `p=2,u=1,lambda=1`, a specialized ordinary Hurwitz integral equals zero, whereas the fixed-power meromorphic spectral limit equals minus one. The full endpoint amplitude explains the discrepancy.
- At negative integral resolvent powers, the smooth endpoint residues cancel, but the removable quotient has a nonzero finite value. Exact residue and cotangent-jet calculations independently prove and check this correction.

These are counterexamples to unqualified extensions, not allegations that the inspected incoming resolvent theorem makes those extensions.

## Independent review

Each major analytic contribution was reviewed independently of its initial derivation. The quartic global contour, endpoint constants, harmonic reduction, and depth-three Mellin identification were checked separately. The mixed-tail constant-term normalization, rational boundary block, ordinary-zeta elimination, analytic EGF, and truncation envelope were also checked. The continuous-power completion, half-plane phases, noninteger corollary, Gamma–Gauss moment theorem, half-power examples, and normalized primitives were reviewed independently.

Two wording refinements from review were incorporated: fixed Taylor jets, rather than unexpanded parameter functions, are finite polynomials in the required zeta/Stieltjes coefficients; and the polylogarithm reduction of the harmonic-tail generator retains its explicit elementary hyperbolic prefactor.

The mathematical review found no remaining mandatory proof correction. The supplied exact checks and independent numerical replay passed. The report does not claim formal proof-assistant verification or interval certification of floating-point results.

