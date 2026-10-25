# Independent arithmetic review of reciprocal pooling

Reviewed on 25 October 2026 against `RECIPROCAL_POOLING.md` and the pinned
package158 `POOLED_POWERS.md` and `STRICT_HORIZON_AND_BETA.md` sources.
This is an independently assigned AI mathematical review, not an external
human review or a new proof-assistant certificate.

## Verdict

The two-consecutive-base theorem is correct under its stated canonical-Pell
and square-frame hypotheses. Its use in the package158 bootstrap is
noncircular. The new residual is an ordinary polynomial. No coprimality
condition between its two moduli is needed.

The remaining implementation obligations are finite: retain the parent
canonical-Pell rows; verify all fourteen exact affine base/output/index
expressions remain in the square frame; verify the four deleted coordinates
are private to the four old pool rows; check the replacement polynomial
coefficient by coefficient. This review establishes the unbounded arithmetic
argument, not those implementation facts.

## Independent reconstruction

Write `D_i=m_i-X_i+Z_i`, `Z_i=A Y_i`, and
`T_j=2 A n_j-n_j^2-1`. For each block define

    H_j = sum Y_i(m_i-X_i),
    S_j = sum (D_i^2-Y_i^2),
    E_j = S_j-2n_j H_j.

Expanding the square directly gives

    sum (D_i-n_jY_i)^2 = E_j-T_j sum Y_i^2.

Thus the new equation is precisely integrality of
`E_0/T_0+E_1/T_1`, which is equivalent to integrality of the sum
of the displayed squared Pell errors divided by their respective moduli.

Let `b=floor(sqrt(W-1))` and `C=(n_0 n_1)^b`. Because every signed index
lies in `[-b,b]`, the cleared integer error

    d_i = C m_i-(C/n_j^b)n_j^(b+k_i)

is well-defined. The canonical-Pell congruence gives
`d_i = C(D_i-n_jY_i) mod T_j`. Hence

    sum_j sum_i d_i^2/T_j

is an integer. In this inference one only multiplies by `C^2` and changes
each numerator by an integer multiple of its own denominator. This is why
neither `gcd(T_0,T_1)=1` nor `gcd(C,T_j)=1` is needed. The only modular
inverse used is that of `n_j` modulo `T_j`, justified by `T_j=-1 mod n_j`.

The uniform bounds are

    |C| <= b^(2b),
    |C/n_j^b| <= b^b,
    |d_i| <= b^(2b+1)+b^(3b) <= 2b^(3b).

Since `r<=15`, `W>=258`, `b>=16`, and `b^2<W`,

    sum_i d_i^2 <=4r b^(6b)<W^(3b+1)<=W^W.

The final exponent comparison follows from `3b+1<=b^2+1<=W`.
Also `|T_j|>=2|A|-W>W^W`. The integer sum of rational errors
therefore has absolute value strictly below1.

Nonzero consecutive integer bases have the same sign. Since
`2|A n_j|>n_j^2+1`, each modulus has the sign of `A n_j`; the two
moduli have the same sign. Their nonnegative squared-error numerators
cannot cancel. The integer sum is zero, so every `d_i=0`, proving the
claimed exact powers after division by the nonzero integer `C`.

For `|n_j|>=2`, a negative index would give the impossible equation
`m_i n_j^(-k_i)=1`. For unit bases, the exact signed power remains the
correct conclusion and no index-sign inference is made.

Conversely, exact powers give `T_j | (D_i-n_jY_i)` by the canonical-Pell
congruence. The square identity then gives `T_j|E_j`, so the stated integer
quotient and the restored old witnesses exist.

## Bootstrap audit

The first three power requests remain outside the new pool. The parent
norm and singleton reasoning proves `|B|>=2`, `H` odd and nonzero,
`x>=0`, and `q=(BH)^x`. Consequently `q` is either1 or has absolute value
at least2. In particular `q!=0,-1`; hence both pool bases are nonzero
before the new theorem is used.

The new theorem simultaneously recovers all q and q+1 requests, including
their possible unit-base cases. Only afterward does `B d=M=q^x` exclude
`x=0`; then the retained ratio `q^t v=q^x` forces `x>=t`. Thus the proof
does not presume the large-base conclusion that it is intended to help
derive. The parent's later factorial and Horn-flow arguments retain their
required hypotheses.

## Scope limitations and useful counterchecks

Same-sign denominators are essential to this argument: denominators2 and
-2 with numerators1 and1 give a zero rational sum without zero errors.
The strict bound is also essential: denominators2 and2 with numerators1
and1 give the nonzero integer1. Neither example satisfies the theorem's
full hypotheses; each isolates the reason a hypothesis is required.

The quotient restoration is integral on solutions. It is not a polynomial
automorphism of the full ambient lattice. A final report should claim
equivalence after existential quantification of private coordinates, not
a bijection between all old and new witness tuples.

The standalone standard-library `check_reciprocal_lemma.py` independently
checks the free-Z polynomial identity for one and two requests, including
the exact defect `2n sum Y_i(Z_i-A Y_i)`, the old-pool elimination identity,
and the two-block recombination. It detects a corrupted modulus constant.
It checks396 small signed-Pell congruences (180 negative-index cases),
eight true-power instances satisfying the full W=258 frame and
`|A|=258^258+1`, and eight perturbed-output negative controls. Both signs
of A and the bases-3,-2,-1,1,2,3 occur. It also demonstrates the two
hypothesis-necessity counterexamples above. Normal and optimized Python
runs pass. These finite tests are supplemental evidence; the preceding
inequalities and rational-integer argument are the proof of the unbounded
lemma.

The degree bound10 and variable savings are valid symbolic bounds for the
unprojected replacement. Exact degree, operation counts, monomial counts,
and compatibility with subsequent projection certificates must be read
from the emitted and independently audited complete equations.
