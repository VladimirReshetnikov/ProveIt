# Proof audit and limitations

This is an internal mathematical review checklist, not an independent referee
report or proof-assistant certificate. The article contains the actual proofs.

## Main dependency checks

1. **Normal convergence and exact zeros.** Positive summable widths imply a
   square-summable tail. On each compact complex set the sinc factors differ
   from one by O(s_k^2). After removing finitely many vanishing factors, the
   remaining product is nonzero; there are no hidden extra zeros.
2. **Arbitrary probability remainder.** Necessity only uses its bounded real
   characteristic function. We do NOT assume analyticity or derivatives of an
   initially unknown remainder. Since all denominator zeros are real, local
   real order domination suffices to remove all quotient poles.
3. **Separated-source classification.** The first positive zero forces a width
   s_k/n. Rational separation makes that form unique. Two assigned factors at
   one coordinate cause a double zero at their denominator lcm, while the
   source zero is simple. Distinct assignments yield a positive independent
   digit/uniform remainder, not just a formal entire quotient.
4. **Countable family handling.** Each selected factor uses a distinct bounded
   source coordinate. All extracted and residual series are absolutely
   convergent. In the Hall proof, finitely many deadlines lie below each bound,
   so sorting an infinite family is a valid exhaustive enumeration.
5. **Geometric parameters.** Comparing the first two terms initially allows an
   integer step m and a positive rational digit ratio d. All later terms force
   k_j=a+mj and n_j=n*d^j. Nonnegative distinct indices force m>=1; integrality
   for every j forces the denominator of d to be one.
6. **One-sided CRT.** An integer progression intersection can always be shifted
   by a common period until both term indices are nonnegative. Density alone
   is not used as a compatibility test.
7. **Resonant channels.** For q=p^(-e/h) with e/h reduced, rational powers occur
   exactly at multiples of h. Source zero classes in distinct residues cannot
   meet. Each channel is the previously known prime-power Hall problem.
8. **Finite orbits.** The rational-power subgroup of rho has generator ell|h.
   Distinct initial residues exhaust its orbit. An integral denominator on
   every return forces rho^ell=1/D. A single channel receives one stream, so
   deadline growth requires and suffices for v_p(D)>=e.
9. **Wasserstein constants.** Uniform width a has E|aU|=a/4 and variance a^2/12.
   Thus its characteristic derivative is bounded by pi*a/2. Source second
   derivative is bounded by pi^2/[3(1-q^2)], giving half that constant in the
   Taylor error. Choosing h=D_q/(2A_q) gives precisely the displayed lower
   bound, without differentiating the unknown remainder.
10. **Parameter transition.** The explicit dyadic remainder is D_3+X_(1/2)/4.
    Shared coordinates bound W1 by |q-r|/[4(1-q)(1-r)]. Delta is continuous;
    the instability concerns exact factorability, not discontinuity of Delta.
11. **Classical singular example.** The golden-ratio remainder is a scaled
    Bernoulli convolution. Nondecaying Fourier values exclude a wholly
    absolutely continuous law. A separate fixed-point/Lebesgue-decomposition
    argument proves pure singularity, and the maximal-atom argument proves
    absence of atoms. These extra steps are needed for “singular continuous.”
12. **Composite obstruction.** The signed base-six quotient has genuinely
    disjoint translated tail supports, so its negative central mass cannot be
    canceled. Entire extension alone is not asserted sufficient in that case.

## Finite verification

The delivered receipt reports 156,227 checks using only exact integers and
rational numbers. CRT is compared with finite-period enumeration; Hall is
compared with independent finite backtracking; finite orbit arithmetic, digit
moments, example assignments, and invalid inputs are checked. Encoded
nonresonant data tests do not decide nonresonance of real numbers.

No finite test proves a universal analytic theorem. No Lean/Rocq build,
validated floating-point proof, or peer review is claimed.

## Explicitly inherited or classical

- Sinc product, interval refinement, and multisection mechanisms.
- Prime-power Hall criterion in the h=1 target.
- The reciprocal-composite base-six entire/nonpositive counterexample.
- Golden-ratio Bernoulli singularity; the zero-dimensional exceptional-set
  theorem cited only as context.

## Not settled

- Least rational returns with numerator >1.
- Complete positive-quotient criteria for composite reciprocal returns.
- All arbitrary probability convolution factors.
- Optimal asymptotics of the Wasserstein approximation error near resonance.
- General regularity classification of digit remainders.
- Exact algebraic-parameter recognition and all proposed formalization work.

No worldwide priority guarantee follows from the focused source inspection.
