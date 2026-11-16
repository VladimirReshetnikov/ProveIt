# Applications audit and weighted-norm contribution

Pinned ProveIt commit: `052fbaebfc955294b4c02f6532ab7e7a3f760f7a`.
All paths below are relative to `Logic/PrimitiveRecursiveArithmetic/docs/proofs/`.

## What is already done, and should not be claimed as new

1. `diophantine-number-theory/mordell_weil_ipra/paper/02_descent.tex` already proves stopped contracting height descent, logarithmic fuel, explicit coefficient output, and quantitative coefficient bounds from a supplied reducing step. It also states the distinction between a finite program description and a universal proof of the program's contract.
2. `diophantine-number-theory/mordell_weil_ipra/paper/03_elliptic.tex`, sections “The supplied-cover constructive elliptic Mordell–Weil theorem” and “An alternative selector using only bounded-height enumeration”, already derives a bounded selector from actual covering representatives and height estimates. The remaining gap is producing actual rational representatives covering the quotient. A finite Selmer bound alone supplies neither realizability of a class nor its representative.
3. `diophantine-number-theory/diophantine_geometry_ipra/sections/07_generation.tex` already gives a more general m-ary height descent and a bounded arithmetic coordinate algorithm.
4. `diophantine-number-theory/siegel_ipra/paper/05_general_route.tex` already proves finite-cover-to-cardinality, gives a bounded search through spans of subtuples, and isolates the needed finite approximation theorem and geometric fiber bound. We should not present the counting or finite-span step as new.
5. `foundations/ipra_embedding_framework/paper/05_diophantine.tex` repairs the geometric fiber bound for odd-degree hyperelliptic curves using a sharp polynomial norm argument; it also develops a general quotient-algebra dimension certificate bounding common zeros.
6. `foundations/ipra_framework/paper/sections/07_diophantine.tex` already generalizes integral square-gap certificates to powers, gives a polynomial power-completion constructor, and transports numerator bounds under a supplied denominator bound.
7. `diophantine-number-theory/faltings_ipra/faltings_ipra.tex` distinguishes list/cardinality/height information, supplies the first-halting-time counterexample, and explains why a positive uniform height theorem would have a primitive-recursive witnessing consequence. None of these logical distinctions should be claimed as newly discovered.

## Identified remaining mathematical obligations

- General Mordell–Weil: actual finite rational quotient representatives (or another equivalent constructive covering interface), with proofs of coverage. The existing final height descent is not the principal remaining gap.
- General Siegel: a finite-tuple quantitative approximation/cover theorem, arithmetic function-space/divisor interfaces, and cover-and-lift control. Its §5 describes a pole-degree/zero-degree argument but does not build it in arithmetic.
- General Faltings: a positive uniform height/complete-list witness, as opposed to a cardinality bound, remains unprovided.
- Puiseux/exact coefficient branching: fast Cauchy names do not supply decidable zero tests. This audit has not tried to remove that known obstruction.

## New contribution relative to these inspected packets

The fully developed argument is in `paper/sections/05_norms.tex`.

Take coprime positive m,d with m≥2, c≠0 rational and

    F(X,Y) = Y^m − c X^d + lower terms of weight m i + d j < m d.

For a nonzero reduced G = Σ_{j<m} A_j(X)Y^j let

    W = max{m i + d j : coefficient of X^iY^j in G is nonzero}.

Then the determinant norm N_G of multiplication by G in Q[X,Y]/F has exact degree W. If a X^kY^j is the unique monomial of maximum weight, its leading coefficient is

    a^m ((−1)^(m−1) c)^j.

This applies to mixed equations, not only y^m=f(x). Every finite list of distinct rational common zeros of F,G has length ≤W, with full point multiplicity when several points share the same first coordinate.

The proof has two reusable mechanisms:

1. **Weighted rescaling of a multiplication matrix.** Put F_t=t^(md)F(t^(−m),t^(−d)Z), G_t=t^W G(t^(−m),t^(−d)Z). These are polynomials in t,Z. At t=0 their quotient norm is the nonzero explicitly calculated norm of aZ^j modulo Z^m−c. Conjugating basis matrices proves D(t)=t^(mW)N_G(t^(−m)), so a nonzero constant coefficient proves exact degree W without cancellation guesses or algebraic branch selection.
2. **Fiber cardinality is determinant multiplicity.** r distinct y-values over x=u give r independent evaluation rows (Vandermonde). Complete these rows with the final standard basis rows to an explicit invertible matrix U. The first r rows of UM_G vanish at u, giving (X−u)^r | N_G. Multiplicities at distinct u multiply, so total point count ≤deg N_G.

This yields an explicit family of finite spaces:

    B_L = {X^iY^j : 0≤j<m, mi+dj≤L},
    n(L) = Σ_{j<m} max(0,1+floor((L−dj)/m)).

For L≥max(0,md−m−d),

    n(L)=L+1−(m−1)(d−1)/2.

The proof is residue arithmetic; do not identify the constant with geometric genus without additional smooth-model hypotheses. Any proper rational subspace of the evaluation space has at most L points above it. Combined with a supplied finite-tuple cover by M proper subspaces, this proves the conditional cardinality bound ML. The cover theorem itself remains missing.

Additional concrete benefits:

- The adjugate identity and nonzero norm prove that Q[X,Y]/F is a domain, giving a decidable exact rational-function representation without initially importing an abstract function-field theorem.
- If coprimality fails, or several leading terms occur in F, the exact finite initial determinant det(mul(G_0) mod F_0)≠0 is still a sufficient certificate for the same degree and point-count theorem. This is an individual-certificate extension, not an assertion that all such curves satisfy it.
- An arbitrary G can be reduced in Y first; if the remainder is nonzero its norm theorem applies. The reduction does not increase weighted degree for the principal family.

## Sharp and multiplicity-sensitive examples

1. F=Y³−X(X−1)(X−2)(X−3), G=Y. Norm is X(X−1)(X−2)(X−3), W=4 and the four common zeros (0,0),(1,0),(2,0),(3,0) attain the bound.
2. F=Y³−Y−X⁴, G=X. Norm is X³ and the three common zeros (0,−1),(0,0),(0,1) are all in one X fiber. This verifies why counting distinct first coordinates alone would lose the sharp theorem.
3. F=Y²−2X⁴−X−1, G=X²+Y. Weights m=2,d=4 are not coprime. The initial determinant is 1²−2=−1, so the certificate succeeds; N_G=−X⁴−X−1 has degree4.

The exact reference checker is `code/check_weighted_norm.py`; its output is `validation/weighted_norm_checks.json`. They verify a fixed deterministic collection of norms and leading coefficients, the dimension formula at and after its threshold, and the three displayed examples. These are finite arithmetic regression checks, not proofs of universal correctness or iPRA derivability.

## Suggested formalization split

The compiled proposition definitions are `NormDegreeGoal`, `FiberPowerGoal`, `CommonZerosGoal`, `WeightedBasisCountGoal`, and `EventualDimensionGoal` in `lean/WeightedNormTargets.lean`. The proper-subspace corollary additionally requires the explicit finite row-elimination construction described in the report. Use a rational polynomial coefficient table, a reduced Y coefficient vector of length m, explicit monic reduction, and permutation-sum determinant as definitions. The required auxiliaries are determinant specialization/conjugation, monic remainder evaluation, Vandermonde determinant, coefficientwise factor removal, and bounded finite-list grouping. A full object-language derivation is still a distinct task from ambient Lean verification. The TeX section records induction invariants and compilation route rather than assuming reflection.

## Exact inspected source URLs

- https://github.com/VladimirReshetnikov/ProveIt/blob/052fbaebfc955294b4c02f6532ab7e7a3f760f7a/Logic/PrimitiveRecursiveArithmetic/docs/proofs/diophantine-number-theory/mordell_weil_ipra/paper/02_descent.tex
- https://github.com/VladimirReshetnikov/ProveIt/blob/052fbaebfc955294b4c02f6532ab7e7a3f760f7a/Logic/PrimitiveRecursiveArithmetic/docs/proofs/diophantine-number-theory/mordell_weil_ipra/paper/03_elliptic.tex
- https://github.com/VladimirReshetnikov/ProveIt/blob/052fbaebfc955294b4c02f6532ab7e7a3f760f7a/Logic/PrimitiveRecursiveArithmetic/docs/proofs/diophantine-number-theory/diophantine_geometry_ipra/sections/07_generation.tex
- https://github.com/VladimirReshetnikov/ProveIt/blob/052fbaebfc955294b4c02f6532ab7e7a3f760f7a/Logic/PrimitiveRecursiveArithmetic/docs/proofs/diophantine-number-theory/siegel_ipra/paper/05_general_route.tex
- https://github.com/VladimirReshetnikov/ProveIt/blob/052fbaebfc955294b4c02f6532ab7e7a3f760f7a/Logic/PrimitiveRecursiveArithmetic/docs/proofs/diophantine-number-theory/faltings_ipra/faltings_ipra.tex
- https://github.com/VladimirReshetnikov/ProveIt/blob/052fbaebfc955294b4c02f6532ab7e7a3f760f7a/Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_embedding_framework/paper/05_diophantine.tex
- https://github.com/VladimirReshetnikov/ProveIt/blob/052fbaebfc955294b4c02f6532ab7e7a3f760f7a/Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_framework/paper/sections/07_diophantine.tex
