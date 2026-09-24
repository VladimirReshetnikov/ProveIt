# Proof audit and dependency checklist

This is an author-side audit, not an independent review or a formal proof.
The numbered references below refer to the definitions/sections of the paper.

## Dependency

The sole non-elementary imported theorem is Jacobsthal's binomial congruence,
in Straub, *Multivariate Apéry numbers and supercongruences of rational
functions*, Lemma 5.1. For an odd prime p its normalized ratio error has
valuation at least v_p(X*Y*(X-Y)) - delta_p, with delta_3=1 and delta_p=0
for p>=5. This is a classical theorem, not an unproved hypothesis.

## Checks on the mathematical argument

1. **Domain and integrality.** A,B may be any integers; K is nonnegative.
   Negative upper binomial entries use the formal-power-series convention.
   All lower entries appearing in the weighted proof are nonnegative.

2. **Zero coefficients.** Fine and coarse binomial coefficients vanish
   simultaneously under common scaling by p. Ratios are used only after
   these zero cases have been removed. No step divides by a zero coefficient.

3. **Local denominators.** When p does not divide j and p divides K, neither
   j nor K-j is divisible by p. All reciprocals used in the off-multiple
   argument belong to Z_(p).

4. **Initial sign.** For a unit index j, the first product descent changes the
   sum of lower indices from K-2 to K/p-1. The sign exponent K-K/p-1 is odd.
   Thus the first coarse weight has a minus sign.

5. **Subsequent signs.** At level ell, the two lower indices add to
   K/p^ell-1. Their coarse sum is K/p^(ell+1)-1. The difference is even
   for an odd prime p, so no additional minus sign occurs.

6. **Complete blocks.** The assumption p^h divides K means there are no
   truncated blocks at any level 1 <= ell <= h. Block endpoints divisible
   by p are excluded automatically from reciprocal-square sums.

7. **Precision bookkeeping.** The weight difference at level ell is
   divisible by p^(h-ell), and its complete harmonic block is divisible
   by p^ell. Their product is divisible by p^h. A single unsupported
   replacement of all weights by a final coarse weight is not used.

8. **Terminal level and h=1.** At ell=h the weight is constant across a
   whole p^h block. For h=1 the intermediate descent is empty, and the
   initial and terminal steps alone give the weighted lemma.

9. **Multiple-index valuation.** With e=min(h,v_p(j)), e>=1. If e<h,
   both j and K-j have valuation e. The coarse binomial product is then
   divisible by p^(2*(h-e)). Jacobsthal's ratio error supplies
   p^(h+2*e-delta_p). The sum of these exponents is 3*h-delta_p.

10. **Endpoints.** At j=0 or j=K, endpoint binomial ratios equal one.
    The choice v_p(0)=infinity puts these in the e=h case.

11. **Off-multiple sum.** Extracting A*B supplies p^(2h).
    Replacing 1/(j*(K-j)) by -1/j^2 costs only an error divisible by p^h.
    The weighted lemma supplies the remaining p^h. This part vanishes
    modulo p^(3h) even when p=3.

12. **Prime 3.** Only the classical ratio estimate loses a power at 3;
    the alternating pairing is valid for every odd prime. Hence the final
    exponent is 3h-1 at p=3, not a conjectural extrapolation.

13. **K=0 and t=0.** Both coefficient sides are one. This case is removed
    before any use of 1/j or 1/(K-j).

14. **Base divisible by p.** No step assumes p does not divide m.
    Additional common divisibility can be absorbed by increasing the height.

15. **Generating-function consequence.** Pairing the d=e and d=p*e terms
    of the Möbius transform gives a sum of tower differences. The denominator
    bound follows prime by prime. Lambert/trilogarithm identities use formal
    coefficient comparison, not analytic convergence or a changed order of
    an infinite numerical sum.

## Computational cross-checks actually run

- 10,930 one-digit binomial descent instances.
- 105 complete alternating harmonic blocks.
- 3,309 multiple-index term comparisons.
- 165 off-multiple sums at the stronger p^(3h) modulus.
- 165 weighted reciprocal-square sums.
- 165 initial-sign comparisons.
- 150 multiscale transitions.
- 165 terminal blocks.

These total 15,154 proof-component checks, in addition to 13,690 family
congruences and 500 transform-denominator checks. The exact code and outputs
are included. They can detect some transcription and sign errors, but finite
checks cannot certify the universally quantified mathematical statements.

## Remaining epistemic limitations

No human referee reviewed the proof and no Lean, Isabelle, or other proof
assistant checked it. No publication-priority claim is made. There is no known
unresolved proof obligation within the written argument; the limitations are
independent verification and the incompleteness of the literature search.
