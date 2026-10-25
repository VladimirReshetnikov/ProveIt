# Independent review of the descending-binomial natural quartic

## Conclusion and review boundary

I reviewed the Cantor-constructor variant of the delivered natural-number
equation and its changes relative to package 129, including the descending
factorial identity, the sign change in the reciprocal CRT moduli, the
single-row Pell cap, and the reduction of the minimum horizon to 12. The
ordinary soundness and completeness arguments are valid with the order of
dependencies set out below. No mathematical objection remained after this
review.

The final object has 233 nonnegative integer variables, 182 quadratic
residuals, exact degree four, 7,313 collected monomials, and coefficient
height 86,543,666. I independently replayed the supplied affine-export and
contraction checkers, without importing the producer or optimizer, and
compared every final coefficient with the delivered expansion. The replay
record and exact file hashes are in `INDEPENDENT_REPLAY.json`.

This is an ordinary mathematical and finite algebraic review. It is not a
new end-to-end Lean/Rocq derivation or an object-language ZFC proof term.
The final consistency interpretation uses the retained C222/ZF/ZFC
calibration identified in the report. This review does not assert the
consistency or inconsistency of ZFC, or a claim of global minimality.

## 1. The descending factorial fixed point

Let t>=3 and F>=2 be integers, put n=F^2-1, and require

    B=binom(n,t)>=2,       n^t=FB+r,       B=r+s+1,

with r,s natural. These rows say exactly F=floor(n^t/B). Since B>=2,
one has n>=t+1. Write T=t! and S=t(t-1)/2. Then

    n^t/B = T / product_(j=0,...,t-1)(1-j/n) >= T.

The floor condition therefore implies F>=T. The elementary estimate
T-1>S holds for t=3 and persists by induction. Consequently

    n >= T^2-1 = (T-1)(T+1) > S(T+1).

All j/n are in [0,1), and the product inequality gives

    product_j(1-j/n) >= 1-S/n > 0.

Thus

    T <= n^t/B <= T n/(n-S) < T+1.

Its floor is T, so F=T. Conversely F=T makes the same strict interval
hold and supplies the unique remainder r=n^t-TB and slack s=B-r-1.
This proves both directions without a consistency assumption.

The new polynomial materializes F as F0+2 and n as
(F0+1)(F0+3), all over naturals. This is exactly F^2-1, with no
subtraction that could invalidate a natural-domain restoration.

### No circular digit bound

The simultaneous Pell argument is applied before interpreting the binomial.
It recovers the exact powers N=B^K and q=N^K with B>=2 explicitly,
R=2+t+x+y+F, and K=2R. Therefore q>=2^(4R^2).

Before the factorial is known, n=F^2-1<R^2 and t<R. For 0<=j<=t,

    binom(n,j) <= n^t < R^(2t) <= 2^(2Rt) < 2^(2R^2) < q,

with binom(n,j)=0 when j>n. This suffices to interpret the sole exact
binomial digit as B=binom(n,t). The fixed-point theorem is used only
after that interpretation. No conclusion F=t! is used in this digit
bound.

## 2. Reciprocal CRT with the descending signs

After F=t! is established, define, in the proof,

    d_i=F^2/i-1,       1<=i<=t.

Since i divides F, each d_i is an integer congruent to -1 modulo F.
It is positive, and every prime divisor of d_i exceeds t. If a prime
divided both d_i and d_j, it would divide
j*d_j-i*d_i=i-j, hence would be at most t; that is impossible. Thus
the d_i are pairwise coprime and

    product_i d_i = product_i(F^2-i)/i = binom(F^2-1,t)=B.

The changed index row is essential:

    C+1 = F^2+Bq_index.

It is not the old ascending-modulus row. Modulo d_i, F^2=i, so this
new row gives C=i-1 modulo d_i. The retained range condition
N|binom(C,t), with N=B^K, then recovers the intended small index i-1
modulo a selected prime power of d_i, exactly as in the earlier range
argument. Since its prime p exceeds t, there cannot be two different
residues in [0,t-1] congruent modulo p.

For completeness the original precision-2K CRT prescription supplies a
positive C<=N^2 with those residues. This also gives
C=F^2-1 modulo B. The required natural quotient exists: for t>=3,
B=binom(F^2-1,t)>F^2. For example, setting n=F^2-1, one has
2<=t<=n-2 and B>=binom(n,2)>n+1=F^2. A positive integer congruent
to F^2-1 modulo this larger B is at least F^2-1, so
(C+1-F^2)/B is nonnegative.

The unchanged local and derived-label range conditions are still decoded
prime by prime. The soundness range lemma is used in its valid direction,
and completeness still uses precision 2K to compensate for division by
the falling-factorial denominator. The transformation does not use the
false converse of the range lemma. The change from +1 to -1 in d_i
changes neither pairwise coprimality nor the fact that its primes exceed t.

## 3. The single-row cap is sound

Write h for the already requested derived-label index J, V=Y_h(A) for
the anchor ordinate, and k_i for the fourteen other requested indices.
The retained full indexed-Pell criterion identifies the anchor once
h<=V is available. The new row is

    V = h + sum_i (y_i-k_i)^2 + (A-1)q_cap,       q_cap>=0.       (C)

The lower-scale norm first proves A>W^W, with h<W, k_i<W and W>=3.
Thus (C) itself supplies h<=V before the anchor criterion is invoked;
there is no circular use of the correct anchor index.

After the anchor has been identified, h>=2 gives V=Y_h(A)>=2A.
Each principal norm, including the consecutive-coordinate presentation,
classifies its nonnegative ordinate as y_i=Y_(j_i)(A) with j_i>=0,
without yet requiring an abscissa orientation. Suppose j_i>=h. Then
y_i>=V, k_i<W<A<=V/2, and V>4. It follows that

    (y_i-k_i)^2 > V^2/4 > V,

contradicting (C). Hence every actual j_i<h<W.

Modulo A-1, the Pell recurrence gives V=h and y_i=j_i. Reducing (C)
therefore shows that A-1 divides

    E=sum_i(j_i-k_i)^2.

There are fourteen seeds, with their count at most W-2. The frame bounds
give 0<=E< W^3 < A-1, so E=0. Thus j_i=k_i for every seed. Each seed
occurs in a retained nonnegative output row whose base is below A; that
row supplies the same consecutive-pair orientation as in package 129.
All exact and modular power requests are therefore recovered correctly.

## 4. The single-row cap is complete

Completeness preserves the semantic-anchor lift from package 129. Starting
from the CRT representatives, increase only the encoded a-column by N^2.
All precision-2K residues are unchanged. The nine independent positive
representatives sum to at most 10N^2, and each is at most 2N^2.
The derived J includes the Cantor constructor I(a,b)>=2a^2, hence

    h=J>2N^4.

All other requested indices are at most 2N^2. For the remaining numerical
indices this follows from N>=4^R and the same elementary bounds on
t,K,x+1,y+1 and F^2-1 as before. Therefore h>2k_max.

Choose every principal ordinate canonically. Let k=k_max>=1 and r be
the number of seeds. Since Y_(k_i)>=k_i,

    sum_i(Y_(k_i)-k_i)^2 <= r Y_k^2.

The standard identity and strict Pell growth give

    Y_(2k+1)=Y_(k+1)^2-Y_k^2 > 4A(A-1)Y_k^2.

As h>=2k+1, h<W<A, and r<=W-2, this implies
Y_h-h-sum_i(Y_(k_i)-k_i)^2>0. Its divisibility by A-1 follows directly
from the Pell congruences. Dividing by A-1 supplies the nonnegative
q_cap in (C). Thus the new cap row does not exclude any canonical
refutation witness after the permitted CRT lift.

The main Pell base is still chosen only after all semantic data and W.
Its separate lower bound leaves it free to satisfy the common-root
congruence. No simultaneous Pell/CRT existence condition has been added.

## 5. Horizon 12 and the unchanged source bounds

The actual Cantor source majorants are E=2^23 and ell=2^22. With
F_min=12!=479001600 and a=floor(log2(F_min))=28, the constructor checks

    aE < 2^a,       2E <= 2^a,
    3 ell (12+1) <= 2*12!.

These are true integer inequalities. They propagate to all larger
horizons. The factorial-to-linear ratio increases; the elementary
inequality R^E<2^R begins at R=2^a and propagates for R>=2E, for example
using (1+1/R)^E<=1/(1-E/R)<=2. Thus the local evaluation remains below
the selected amplified prime-power modulus. The derived-label digit
bound continues to hold after the 10N^2 representative budget because
10<16 and 3ell(t+1)<=2F<K. Padding a finite refutation to any sufficiently
large t remains available. No source rule specifically requires t>=16.

## 6. Exact algebra and finite controls

The independent affine audit checked every defining gate and dependency
closure, all 692 unexported rows, the 400 nonnegative affine restorations,
all 288 raw quadratic rows in 339 variables, and all 5,000 coefficients
of their sum of squares. It rejected the five supplied actual corruptions
of a coefficient, affine definition, output-coordinate order, gate map,
and output-row inventory.

The separate contraction replay checked all 106 monic restorations,
including the two with negative coefficients justified by exact rational
sums of squares. It restored every deleted coordinate in the natural
domain, matched every one of the 182 final residuals and all 233 variable
names, and compared all 7,313 coefficients in the final expansion.

An additional small script, `review_arithmetic_controls.py`, independently
checks 2,197 factorial candidates, ten descending reciprocal products,
and 2,452 small single-row-cap tuples, as well as the horizon-12 initial
inequalities. Only the four intended cap tuples are accepted in those
tests. These are implementation controls. The preceding unbounded proofs,
not those samples, justify the quantified mathematical claims.

The retained engine contains historical parent reports and verification
scripts as provenance. Their old ascending-factorial statements are not
claims about this changed polynomial. The current construction, this
review, the current report, and the explicit endpoint replay identify the
new theorem and the scopes of the checks that were actually run.
