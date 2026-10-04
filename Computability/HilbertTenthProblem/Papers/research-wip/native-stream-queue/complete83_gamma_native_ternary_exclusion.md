# A native ternary exclusion for the independent-gamma83 power tests

The exact half-binomial formula gives an explicit digit class on which **neither** of the two [power-congruence tests](complete83_gamma_power_tests.md) can ever succeed, regardless of how many times its starting residue is squared. On every genuine compiler history in this class, the fixed-history alias modulus satisfies **v3(m)=2 exactly**. The result uses no factorization of the enormous native modulus H.

This sharpens the earlier ternary residue and local-order filters. It does **not** prove that a genuine compiler history enters this class, exclude the tests on all histories, or settle the ordinary-input language of [independent-gamma83](complete83_independent_gamma_scout.md). No circuit or universal arithmetic bound changes.

## 1. Exact statement and inherited domain

At a genuine positive parent history use the existing notation

    R=3 mod4, r=(R−1)/2,
    X=2^R, 2Y=sum_(j=0)^r binom(2r,r+j) X^j,
    a=Y(X+1), Delta=(a+1)(a+3), H=4a+3,
    O=ord_H(2), g=gcd(2Delta,O), m=g/gcd(g,2d).

The unchanged native kernel gives q=2^t>=16, the prescribed range/population of R, and the displayed exact half-binomial Y. The fixed compiler has d a positive power of5. The earlier [period theorem](complete75_independent_gamma87_period.md#3-a-uniform-ternary-index-obstruction) already proves

    a=6 mod9 iff the ternary digits of r are only0/1 and r=0 mod3;
    otherwise a=0 mod9.

Restrict to its first digit class. Write

    r=sum_j b_j 3^j, b_j in{0,1}, b_0=0,
    s=sum_j b_j, z=sum_j b_j*b_(j+1), epsilon=b_1,
    e=s+2z mod6.

All missing higher digits are zero. Since r is odd, s is odd, so e is1,3 or5. The new exact table is

| epsilon | e=1 | e=3 | e=5 |
|---:|---:|---:|---:|
|0|a=15 mod27|a=6 mod27|a=24 mod27|
|1|a=24 mod27|a=15 mod27|a=6 mod27|

In particular,

    a=6 mod27 iff e=3+2epsilon mod6.                    (1)

For every genuine history satisfying this digit condition,

    v3(Delta)=2, v3(H)>=3, v3(g)=v3(m)=2.               (2)

Both congruences below fail for every natural e0, including zero:

    2^[2^e0(H−1)] !=1 mod H,
    2^[2^e0(H−3)] !=1 mod H.                            (3)

Here e0 is the number of repeated squarings, unrelated to the digit residue e in the table. The claim is universal on the specified exact native digit class. Finite unsuccessful tests are not used to infer (3).

## 2. Central binomial coefficients modulo9

First, for any nonnegative r whose ternary digits are0/1, without the oddness or final-zero restriction,

    binom(2r,r)=2^(s+2z) mod9.                          (4)

There is no carry in the ternary addition r+r, so the central coefficient is a unit modulo3. This also follows directly from the factorial valuation formula: its valuation is the difference of the ternary digit sums, divided by2, which is zero.

Put F(n)=product_(1<=j<=n, 3 not dividing j) j. Removing multiples of3 from factorials, and using floor(2r/3)=2floor(r/3), gives the exact unit recursion modulo9

    binom(2r,r) = [F(2r)/F(r)^2] * binom(2floor(r/3),floor(r/3)).

Inverses exist because F has no factors of3. The product of the six units in a complete interval of length9 is −1 modulo9. If t=r mod9 is0,1,3 or4, then 2t<9, so complete-interval signs cancel in F(2r)/F(r)^2. Direct multiplication of the at-most-eight residual factors gives

| (b_j,b_(j+1)) at a recursion level | t | F(2r)/F(r)^2 mod9 |
|---|---:|---:|
|(0,0)|0|1|
|(1,0)|1|2|
|(0,1)|3|1|
|(1,1)|4|8|

Iterate through the ternary digits. Every digit1 contributes2, and every adjacent11 pair multiplies that contribution by4. Their product is exactly (4). This is an unrestricted coefficient identity on the stated digit class, not a numerical approximation to Y.

## 3. Expanding the actual tail at X=−1

Define the integral polynomial

    G_r(X)=sum_(j=0)^r binom(2r,r+j) X^j,
    C_r=binom(2r,r).

Two exact identities are

    G_r(−1)=C_r/2,
    G'_r(−1)=binom(2r−2,r−1)=r*C_r/[2(2r−1)].            (5)

The first pairs the two halves of (1−1)^(2r). For the derivative, write j=k−r, use k*binom(2r,k)=2r*binom(2r−1,k−1), and apply

    sum_(k=h)^n (−1)^k binom(n,k)=(−1)^h binom(n−1,h−1)

to the two resulting tails. Their difference is precisely the second central coefficient in (5).

Now r is a positive multiple of3. Therefore the second expression in (5) is divisible by3: its numerator contains r, and its denominator is a unit modulo3. Put delta0=X+1. Since R is odd, delta0 is divisible by3. Taylor expansion of the integral polynomial at −1 gives

    a=delta0*G_r(−1+delta0)/2
     =delta0*C_r/4 + delta0^2*G'_r(−1)/2 mod27
     =delta0*C_r/4 mod27.                               (6)

Every higher term has a factor delta0^3; the derivative term vanishes modulo27 as well. Division by2 or4 means the corresponding unit inverse modulo27.

The low ternary digits give r=3epsilon mod9 and R=1+6epsilon mod18. Since2 has period18 modulo27,

    delta0/3 = 1 mod9 if epsilon=0,
    delta0/3 = 7 mod9 if epsilon=1.

Combine (4)-(6), with 4^(-1)=7 mod9. For epsilon0 the three possible values of a/3 are5,2,8; for epsilon1 they are8,5,2. This proves the entire table and (1).

## 4. Exact alias component and all-squaring exclusion

If a=6 mod27, then a+1 is prime to3 and a+3=9 mod27. Thus v3(Delta)=2. Also H=4a+3 is divisible by27. If h=v3(H), the exact local order is

    ord_(3^h)(2)=2*3^(h−1).

The inherited proof derives this by the elementary lifting identity v3(4^n−1)=1+v3(n). Since h>=3 and 3^h divides H, its order divides O and forces9|O. The gcd with2Delta therefore has valuation exactly2. The actual d is a power of5, so division by gcd(g,2d) removes no factor of3. This proves (2), including its upper bound; factors at other primes of H cannot make v3(g) exceed v3(Delta)=2.

For direct proof of (3), note that H−1 is prime to3, while H−3=4a has valuation1. Multiplication by any power of2 preserves these valuations. Neither candidate exponent is divisible by9. But every exponent giving1 modulo H must be divisible by the local order and hence by9. Both tests are impossible for every e0.

Equivalently, the earlier power-test implications would force m=1 or m|3, contrary to v3(m)=2. For a history in this class, any allowed fixed-history ordinary-input difference is divisible by9. In particular the proposed downward transfers4→3 and4→1 cannot use that same history. This does not exclude other accepted histories, other input differences, or other mechanisms for an incorrect input.

The [actual compiler parity filter](complete75_gamma87_compiler_order_filters.md#2-consequences-for-every-packed-history-of-that-compiler) supplies another necessary condition: a history in this digit class must have odd duration N, an even window-selector count, and an even tile-alphabet size. These are inherited necessary conditions, not sufficient constructions. They do not establish that the new class occurs on any computation of the fixed even-input compiler.

## 5. Bounded evidence and remaining question

The [fresh helper](complete83_gamma_native_ternary_exclusion.py) authenticates eight frozen data/proof files, including the actual83 source receipt and the preceding power-test trio. It never imports or executes predecessor Python. The [receipt](complete83_gamma_native_ternary_exclusion.json) records:

* All128 central coefficients for ternary0/1 words of at most seven digits, evaluated as exact integer binomial coefficients and compared to(4).
* Both polynomial value/derivative identities at128 positive r.
* All32 members of the stated native digit class with odd r<2001, comparing direct binomial tails modulo27 with an independent whole-row prime-power recurrence modulo81. Eleven lie in the exclusion subclass.
* Complete orders for64 freely chosen small arithmetic hosts a=54j+6, confirming v3(m)=2 for d=5,25,125 and finitely corroborating both power-test failures. These hosts are not called native histories.
* One exact half-binomial parameter with R=511999 and q=32. Here r=255999 has ternary spelling 111000011110, s=7, z=5, epsilon1, e5, and a=6 mod81. Streaming all511,999 binomial coefficients with separate3-adic valuation/unit data confirms the residue without constructing X,Y or H.

The last parameter satisfies R=3 mod4, 3q+1<=R<q^4, and popcount(R)=17=3*5+2; hence its native valuation is v2(a)=15. These are genuine numerical kernel prerequisites. **No fixed compiler masks, temporal transport, computation or full polynomial zero are supplied.** In particular this example is not a genuine compiler history for the ordinary input4 or any other input.

The result narrows one sufficient route to a language refutation: histories in the explicit digit subclass cannot satisfy either proposed power test. Occurrence or exclusion of those tests outside the class remains unresolved. Nothing here supplies a global bound on m or changes the status of independent-gamma83.

The bounded CLI uses explicit exception checks, rejects duplicate/nonfinite JSON, and compares receipts recursively with exact types. From any directory:

    python3 /absolute/path/complete83_gamma_native_ternary_exclusion.py \
      --root /absolute/path/native-stream-queue \
      --expect /absolute/path/complete83_gamma_native_ternary_exclusion.json
    python3 -O /absolute/path/complete83_gamma_native_ternary_exclusion.py \
      --root /absolute/path/native-stream-queue \
      --expect /absolute/path/complete83_gamma_native_ternary_exclusion.json

Use --output FILE instead to write the deterministic receipt. Fresh normal and optimized exact replays from / passed. No repository or frozen predecessor bytes were changed.
