# Prime-index reductions for the native half-binomial parameter

The exact half-binomial formula obeys two simple index reductions modulo every odd prime. They remove paired prime factors from R, or powers of a prime from R−1, without constructing the enormous native integer a. A specialization applies to the **actual canonical compiler congruence**, including its mandatory five-power divisibility.

These are unrestricted formula identities, and hence apply to any genuine history satisfying their stated arithmetic hypotheses. They do not show that an arbitrarily selected R is realizable as a history. They supply no bound on the full order gcd and do not settle the ordinary-input language of [independent-gamma83](complete83_independent_gamma_scout.md). No circuit or universal operation count changes.

## 1. Definitions and the scaling theorem

For every positive odd integer R define

    r=(R−1)/2, X_R=2^R,
    C_R=binom(R−1,r),
    a_R=(X_R+1)/2 * sum_(j=0)^r binom(2r,r+j) X_R^j.

Here C_R denotes a central binomial coefficient, not the source's native content word C. For R>=3, a_R is an integer; on genuine native indices it is precisely the parameter recovered by the [half-binomial kernel](pell_kernel_half_binomial42.md). The auxiliary base case R=1 has a_1=3/2; we use it only in the ring Z[1/2] and modulo odd primes. It is not a kernel zero.

Let p be any odd prime and K any positive odd integer. No assumption p not dividing K is required. Put

    lambda = (−1/p), sigma = (2/p),

with each quadratic character interpreted as the integer +1 or −1. Then

    C_(pK) = lambda C_K mod p,
    2a_(pK)−C_(pK) = sigma(2a_K−C_K) mod p.              (1)

Equivalently,

    a_(pK) = sigma a_K + (lambda−sigma) C_K/2 mod p.      (2)

Division by2 is legitimate modulo the odd prime. Iterating gives, for every e>=0,

    C_(p^e K) = lambda^e C_K mod p,
    a_(p^e K) = sigma^e a_K
               +(lambda^e−sigma^e) C_K/2 mod p.          (3)

In particular,

    a_(p²K)=a_K mod p, C_(p²K)=C_K mod p.                (4)

The second reduction is

    a_[p(K−1)+1]=a_K mod p,
    C_[p(K−1)+1]=C_K mod p.                             (5)

Thus the same equalities hold with p replaced by any positive power of p in (5), by iteration. These formulas are exact consequences of the native polynomial; they do not replace a_R by a freely chosen arithmetic host.

## 2. Proof by one base-p digit of the actual tail

The only coefficient fact needed is

    binom(pn+d, pj+ell)=binom(n,j) binom(d,ell) mod p,
    0<=d,ell<p.

It follows by comparing coefficients in
(1+z)^(pn+d)=(1+z^p)^n (1+z)^d over the prime field. In particular,
binom(p−1,ell)=(−1)^ell mod p. This is the same prime-field digit identity underlying the older [native residue algorithm](complete75_gamma87_compiler_order_filters.md#3-computing-a-modulo-a-prime-without-constructing-y-or-h); the present result extracts closed recurrences for specific index shapes.

Write k=(K−1)/2, h=(p−1)/2 and x=2^K mod p. Fermat gives
2^(pK)=x mod p. Define the full-index upper tail

    T_K(x)=sum_(j=k)^(K−1) binom(K−1,j) x^j.

Then

    a_K=(1+x) T_K(x)/(2x^k) mod p.                      (6)

For the index pK, the top binomial argument is p(K−1)+(p−1), and the threshold is pk+h. Separating the final base-p digit gives the central coefficient

    C_(pK)=binom(K−1,k) binom(p−1,h)
           =lambda C_K mod p.                          (7)

Assume first x is not −1. The complete and upper-half sums of the low-digit weights are

    L=sum_(ell=0)^(p−1) (−x)^ell =1,
    U=sum_(ell=h)^(p−1) (−x)^ell
      =[(−x)^h+x]/(1+x).

Euler's criterion gives x^h=sigma because K is odd, and
(−x)^h=lambda*sigma. Every high digit greater than k uses the complete low sum; the equal high digit uses the upper-half low sum. Therefore

    T_(pK)(x)
      =T_K(x)+C_K x^k [lambda*sigma−1]/(1+x) mod p.       (8)

The new threshold pk+h satisfies x^(pk+h)=x^k*sigma. Substitute (8) into (6) for the larger index:

    a_(pK)=sigma a_K + sigma(lambda*sigma−1) C_K/2
           =sigma a_K +(lambda−sigma) C_K/2 mod p.

Together with (7) this proves (1)-(2).

The exceptional case x=−1 must not divide by 1+x. Both a_K and a_(pK) are zero modulo p directly from their defining factor X+1. Also
sigma=x^h=(−1)^h=lambda, so the correction term in (2) is zero. Equation(7) remains valid, and both conclusions follow in this case as well. This covers all odd p,K, including p=3.

For (5), put R=p(K−1)+1. Now R−1=p(K−1), the threshold is pk, and the final base-p digit of the top binomial argument is zero. Only summation positions divisible by p contribute modulo p. The entire upper tail and central coefficient reduce to those at K, while
2^R=2^K mod p and x^(pk)=x^k. Formula(6) therefore gives (5), with no division by 1+x even when x=−1.

## 3. An exact specialization on canonical compiler histories

The [actual modified compiler](complete75_half_binomial_compiler.md#6-five-adic-control-of-the-actual-index) constructs canonical histories with

    d=5^a, h=5^b, Htime=5^f with Htime>=25,
    N=h*Htime, R=dh mod dN.

All four quantities d,h,Htime,N are pure powers of5; Htime is the padded time-height parameter, not the native modulus H=4a_R+3. The required width/height padding and ignored-dummy adjustment are those of the existing compiler. This paragraph assumes a history actually produced with that canonical congruence, rather than asserting it for every noncanonical positive zero.

Since 0<dh<dN and R>0, there is a nonnegative integer z with

    R=dh+dN*z=5^(a+b)(1+5^f z).                        (9)

Consequently

    v5(R)=a+b exactly, K=R/5^(a+b)=1+5^f z.

The equality of valuations uses 5 dividing Htime. It is not obtained by erasing an arbitrary cofactor. The recovered R=3 mod4 and the fact that every five-power is1 mod4 further give z=2 mod4. In particular z+1 is a positive odd index.

For p=5, lambda=1 and sigma=−1. Apply (3) to the leading factor 5^(a+b), then apply (5) f times to K=1+5^f z. The actual native residue is therefore

    a_R = a_(z+1) mod5                    if a+b is even,
    a_R = C_(z+1)−a_(z+1) mod5            if a+b is odd,
    C_R = C_(z+1) mod5.                                (10)

Here z is exactly (R−dh)/(dN), equivalently (R/(dh)−1)/Htime.
All hypotheses needed to remove the entire Htime factor are explicit in (9). If d,h or Htime had other prime factors, that removal would need a different argument.

Formula(10) is an exact necessary residue identity on every such canonical history. It makes no claim that z can be prescribed independently of the accepted computation, masks, packing or dummy choices. It also does not compute the multiplicative order of2 modulo H.

## 4. What the reduction does and does not decide

Let a residue a_R mod p be obtained from these identities, optionally evaluating the smaller-index tails with the existing prime-field digit algorithm. If

    (a_R+1)(a_R+3) is nonzero mod p,

then p does not divide Delta and hence does not divide the odd-prime part of g=gcd(2Delta,ord_H(2)) or the alias modulus m. If 4a_R+3=0 mod p, then p divides the genuine H; its exact order of2 supplies the same kind of lower-divisor certificate described in the older order-filter packet.

These are residue filters. A factor of Delta need not occur in the order. A factor of H does not by itself make that same prime divide g. The identities do not give a uniform small bound on g, and knowledge only modulo5 cannot bound a higher five-adic valuation.

In particular the tempting unrestricted estimate

    v5(Delta_R)<=v5(R)

is false for the exact half-binomial formula. Two independently computed modular examples are

| R | v5(R) | a_R mod625 | Delta_R mod625 | v5(Delta_R) |
|---:|---:|---:|---:|---:|
|395|1|274|550|2|
|4575|2|372|500|3|

The nonzero residues modulo625 determine the displayed valuations exactly. They are not lower-bound estimates from an insufficient modulus. The full enormous a_R is unnecessary.

These are **formula samples only**. They supply neither full kernel tuples nor compiler histories. Their residual cofactors R/5^v5(R) are79 and183, neither1 modulo25, so they do not satisfy the canonical cofactor hypothesis in (9). They refute the unrestricted formula estimate, not an estimate restricted to the full canonical compiler domain.

Finally, the old dummy-control theorem does not supply arbitrary modular control of R. At fixed q every permitted low-dummy change has

    delta R = −Gamma B^i,
    Gamma=(inner radix)^e * (q²−1)
          * [1+q(DC+B*DR+B^h)].

Thus its residue modulo any divisor of q²−1 is locked by the fixed masks. The existing five-adic controller works because Gamma is a unit modulo dN; it cannot simply be reused at an arbitrary odd modulus. This is an inherited restriction, not a new no-go theorem for every possible padding strategy.

A compiled-history false input still needs the full period compatibility and positive width criterion. The present exact index reductions do not prove that compatibility, do not eliminate the unexplored prime factors of the order, and do not establish a positive soundness invariant for independent-gamma83.

## 5. Fresh checks and replay

The [helper](complete83_gamma_native_prime_scaling.py) authenticates seven frozen source/proof dependencies as inert data, including the actual83 source receipt and the five-adic compiler theorem. Its [receipt](complete83_gamma_native_prime_scaling.json) contains:

* 160 one-prime checks, for ten odd primes and sixteen odd K, comparing exact integer binomial coefficients with the scaling identities. Twenty-one cases have x=−1 and explicitly check the exceptional branch.
* 160 checks of the zero-suffix identity(5), and80 checks of iteration and square-factor removal.
* Twelve numerical instances of the congruence shape(9), compared by an independent whole-row prime-power evaluator. They are not claimed complete histories.
* Two independent evaluations modulo625 of each valuation counterexample. One uses exact integer binomial coefficients in the upper half; the other streams the whole row with the prime-adic valuation and unit stored separately.
* Two symbolic consequences at R=3*5^1000 and R=3*5^1001. Their residues are obtained by the proved recurrence; their enormous tails are explicitly not independently materialized. They are not compiler histories.

No predecessor Python, archived code, historical suite or arbitrary-program compiler is executed. No new complete source is emitted. Checks use explicit exceptions, strict byte pins, duplicate/nonfinite JSON rejection and recursively type-exact receipt comparison.

    python3 complete83_gamma_native_prime_scaling.py --root ABS_WIP --expect ABS_JSON
    python3 -O complete83_gamma_native_prime_scaling.py --root ABS_WIP --expect ABS_JSON

Use --output FILE instead to write the deterministic receipt. Fresh normal and optimized exact replays from / passed. All repository and frozen predecessor bytes remain unchanged.
