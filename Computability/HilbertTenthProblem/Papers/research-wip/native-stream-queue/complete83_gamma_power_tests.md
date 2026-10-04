# Width and power-congruence tests for independent-gamma83

Two exact congruence tests reduce a possible refutation of [independent-gamma83](complete83_independent_gamma_scout.md) to a question about the genuine native half-binomial modulus. They need neither its factorization nor its exact multiplicative order. For the fixed compiler of the decidable language of positive even inputs, **any** genuine accepting history at ordinary input4 satisfying either test below would give a full positive zero at a rejected input. Both shifts go downward, so the original positive width bound is preserved automatically.

**Occurrence of either test on an actual compiler history is unproved.** This is a conditional criterion, not a language refutation, a soundness proof or a new universal bound. The [helper](complete83_gamma_power_tests.py) and [receipt](complete83_gamma_power_tests.json) emit no new arithmetic circuit and leave the frozen83 packet unchanged.

## 1. Exact finite input fiber and the width threshold

Fix a genuine positive parent84 zero at ordinary input x0, and pass to independent gamma as in the pinned scout. Use its notation

    Delta=(a+1)(a+3), H=4a+3, O=ord_H(2),
    g=gcd(2Delta,O), m=g/gcd(g,2d).

The native proof gives 6|a. Thus Delta is odd; H is odd and divisible by3; O is even. Consequently

    v2(g)=1, and m is odd.                              (1)

The exact fixed-history alias theorem says that another ordinary input x has a positive completion precisely when

    x>0, x=x0 mod m, alpha0+2d*(x0-x)>0.                (2)

All other outer/main/auxiliary coordinates, including the independent positive gamma, are fixed. The positive input Pell witnesses delta,rho are refreshed by CRT. This is a theorem about the full83 polynomial on these fibers, not just its isolated input congruence.

Let

    A_width=floor((alpha0-1)/(2d)).

The exact set in (2) is

    {x: 1<=x<=x0+A_width, x=x0 mod m},

and its cardinality is

    1+floor((x0-1)/m)+floor(A_width/m).                  (3)

In particular a distinct alias exists if and only if

    m<=max(x0-1,A_width).                               (4)

No amount of enlarging the input Pell index alone changes this finite set: that changes delta,rho, while H,g,m and the width remain fixed. Canonical padding supplies alpha0>q/6, but changes the packed index and hence H and m as well. Padding alone does not prove (4).

## 2. Two exact gcd identities

For every even a divisible by3,

    gcd(2Delta,H-1) = 2*gcd(a+3,5) in {2,10},
    gcd(2Delta,H-3) = 6.                                (5)

Indeed H-1=2(2a+1), and

    4Delta-(2a+1)(2a+7)=5.

The odd common divisor of Delta and 2a+1 is therefore exactly5 when a=2 mod5, and1 otherwise. For the second identity, H-3=4a and `gcd(Delta,a)=gcd(3,a)=3`. These are identities for the actual arithmetic parameter; no primality or factorization hypothesis on H has been inserted.

The inherited compiler uses powers of5 for b,L,d=bL. Its radix condition `2^b>=16` forces b>=5, hence

    5|d.                                               (6)

This follows from the actual [modified compiler recipe](complete75_half_binomial_compiler.md#1-fixed-layout-and-modified-masks), not merely from a freely chosen diagnostic value of d.

## 3. Period certificates and cancellation of powers of two

For any positive integer k, either of the following tests is sufficient for the stated alias divisibility:

    2^[k(H-1)]=1 mod H  ==>  m|k,
    2^[k(H-3)]=1 mod H  ==>  m|3k.                      (7)

Here the modular exponent is an external mathematical test, not an unpaid gate in the polynomial. To prove (7), let B0 denote H-1 or H-3. The test gives O|kB0 and hence `g|gcd(2Delta,kB0)`. For each prime p,

    v_p(g)<=v_p(k)+v_p(gcd(2Delta,B0)).

Divide out the part shared with2d. In the first case (5)-(6) remove the entire possible factor2 or10, leaving m|k. In the second case the only remaining extra factor is3, leaving m|3k. This argument includes prime powers, not just radicals.

Since m is odd by(1), k can be replaced in the conclusion by its odd part. In particular for any e>=0,

    2^[2^e(H-1)]=1 mod H  ==>  m=1,
    2^[2^e(H-3)]=1 mod H  ==>  m|3.                     (8)

Equivalently, start with `2^(H-1) mod H` or `2^(H-3) mod H` and repeatedly square. Reaching1 supplies the corresponding certificate. A prescribed number of unsuccessful squarings proves only failure for those tested e; it is not a claim about all e or all histories.

The second condition is weaker than the earlier sufficient factorization class H=3p with p>3 prime: in that class Fermat's theorem gives `2^(H-3)=1 mod H`. The congruence can be checked directly without proving that factorization. No occurrence of either condition for the genuine native H is asserted.

## 4. A fixed decidable compiler and fixed downward false inputs

Compile the c.e. language S={positive even integers} using the unchanged valid numeral recipe. Its internal even-input normalization recognizes `2S`; the x below is the ordinary input of the84/83 polynomial. Fix x0=4 and **any actual positive parent84 zero** at that input. Such zeros exist by the inherited completeness theorem. Its H remains the one computed from that actual native history.

If the first test in(8) holds, set x=3. Since m=1, (2) holds and

    alpha_new=alpha0+2d>0.

If the second test holds, set x=1. Since m|3, (2) again holds and

    alpha_new=alpha0+6d>0.

In either case the general input-Pell completion supplies strictly positive delta,rho; the other sixteen supplied witnesses remain positive; all six noninput factors preserve their parent values; the input norm equals1; and the full83 output is zero. The new x is odd, so the fixed compiler's intended language rejects it. This would be a full valid-compiler false input, not merely a failed inverse or a zero of a subsystem.

The implication is conditional on the test at that genuine H. It does not select H independently, assume a prime cofactor, change the ordinary-input compiler, or assert that a small diagnostic parameter occurs in its history. Using downward inputs removes the width obstruction for these particular tests, but does not supply the missing number-theoretic existence argument.

## 5. Native valuation and the remaining constraint

For the exact native half-binomial formula, write r=(R-1)/2 and

    X=2^R,
    2Y=sum_(j=0)^r binom(2r,r+j) X^j,
    a=Y(X+1).

The central coefficient has valuation `v2(binom(2r,r))=popcount(r)` by the factorial valuation formula. Every j>=1 term is divisible by2^R, and `popcount(r)<R`, so the central valuation cannot cancel. Since X+1 is odd,

    v2(a)=popcount(R)-2.                                (9)

At a genuine native zero, the exact mask population is `popcount(R)=3t+2`, with q=2^t. Thus

    v2(a)=3t,  H=3 mod 4q^3.                            (10)

These properties reinforce that H is highly constrained. They do not imply a bound on the odd part of g, or either power test in(8). The fixed compiler also constrains R through the actual words, masks and temporal congruence. Small even multiples of3, or small values of the half-binomial formula alone, are not full compiler histories.

The remaining concrete target is now: find one genuine history at ordinary input4 for the fixed even-language compiler whose H satisfies either test in(8), or prove a structural exclusion. A computability or self-reference argument cannot simply choose its future history modulus; the padding and dummy adjustments change R and H. No such occurrence or exclusion is proved here, and independent-gamma83 remains unresolved.

## 6. Fresh bounded checks

The helper authenticates eight frozen source/proof dependencies, including the actual83 trio, actual84 JSON, period theorem and compiler recipes. It reads them only as data. No predecessor Python, archived code, old compiler or historical suite executes.

It verifies the elementary coefficient identity in Section2 and, for256 small a=6,12,...,1536, independently computes the exact order of2 by direct modular iteration. Across d=5,25,125 it checks24,576 general-k tests, including4,653 passing cases, the prime-power divisibility implications and the power-of-two specializations. An independent finite enumeration checks17,280 instances of the exact interval/cardinality theorem.

Three input components illustrate the certificates: a=12,H=51 and a=48,H=195 satisfy the H-3 test; a=1092,H=4371 satisfies the H-1 test. The first two include fully materialized positive input-Pell completions at indices405 and5013. The last checks only modular CRT compatibility; its much larger Pell pair is not materialized. **None is a compiler history or a full83 zero.**

Eight exact evaluations of the half-binomial formula, at R=7,11,15,19,23,27,31,63, check(9) and record the power tests for e=0,1,2,3. They supply no compiler masks or histories; their valuations are below the genuine q>=16 range. All recorded tests there fail, which is only a finite arithmetic observation, not a theorem excluding the tests on genuine histories.

Run from any working directory:

    python3 complete83_gamma_power_tests.py --root /absolute/path/native-stream-queue --expect /absolute/path/complete83_gamma_power_tests.json

`--output PATH` writes the deterministic receipt. Explicit exception checks and recursively type-exact JSON comparison are used in normal and optimized Python. Fresh normal and `python3 -O` exact replays from `/` pass. No repository or frozen predecessor file is modified.
