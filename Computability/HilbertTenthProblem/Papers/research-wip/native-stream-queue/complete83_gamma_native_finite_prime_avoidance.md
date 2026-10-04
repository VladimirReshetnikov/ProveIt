# A finite native prime filter on genuine accepting histories

Fix any accepted positive input of any inherited fixed compiler. Fix an adequate canonical spatial padding h, and put E=dh, where the compiler's fixed d and the chosen h are powers of five. There are genuine accepting histories, with fresh positive witnesses for the unchanged 84-operation parent and its independent-gamma83 forward chart, such that

```
gcd(Delta, 2^(2E)-1) = 3,
gcd(Delta, (2^(2E)-1)/3) = 1,
v3(m) <= 1,
m = gcd(2Delta, ord_H(2)) / gcd(gcd(2Delta, ord_H(2)), 2d).
```

Consequently m is coprime to (2^(2E)-1)/3 on those histories. The construction first fixes h, then the finite prime set, and only then enlarges the time padding. It does not substitute a freely chosen index or modulus for an actual history. There is also an unconditional part: **every canonical history with this h satisfies gcd(Delta,2^E+1)=3**.

This is a structural restriction on some genuine accepting witnesses. It neither bounds the remaining prime factors of m nor settles the ordinary-input language of [independent-gamma83](complete83_independent_gamma_scout.md). No polynomial, supplied coordinate, fixed program numeral, or paid operation count changes.

## 1. Native parameters and the unconditional factor

Use the actual canonical congruence from the [modified compiler, Section 6](complete75_half_binomial_compiler.md#6-five-adic-control-of-the-actual-index):

```
d=5^a, h=5^b, Htime=5^f >=25, N=h Htime,
R = dh mod dN,
R = E(1+Htime z), E=dh, z>=0.
```

The native index is 3 modulo 4. Since all these powers of five are 1 modulo 4, z is 2 modulo 4 and R/E is odd. The exact native formula is

```
r=(R-1)/2, X=2^R, C_R=binom(2r,r),
G_r(X)=sum_(j=0)^r binom(2r,r+j) X^j,
2Y=G_r(X), a=Y(X+1),
Delta=(a+1)(a+3), H=4a+3.
```

Here C_R is a binomial coefficient, distinct from the content word used below. On native indices Y is an integer. Because R/E is odd,

```
2^E+1 divides 2^R+1, hence divides a,
Delta = 3 mod (2^E+1).
```

The elementary lifting identity gives v3(2^E+1)=v3(2+1)+v3(E)=1. Therefore

```
gcd(Delta,2^E+1)=3,
gcd(Delta,(2^E+1)/3)=1.                         (1)
```

This applies to every canonical history, without new switches. In particular it excludes every prime other than 3 whose order of 2 is 2*5^j with 5^j dividing E. The fresh checks confirm ord_11(2)=10 and ord_251(2)=ord_4051(2)=50. The exact factorizations are

```
2^5+1  = 3*11,
2^25+1 = 3*11*251*4051.
```

The full gcd statement (1) does not require factoring 2^E+1.

## 2. A finite simultaneous digit controller

We extend the upper-bit construction in [the genuine ternary escape](complete83_gamma_native_ternary_escape.md). All notation and ignored-bit permissions here are those of that same compiler. Its inner radix r0=2^b is at least 32, its cell radix is B=2^d, q=B^N, and the chosen ignored digit e_* is allowed to be 0,1,2,3. Its lower and upper bits are independent. Put

```
Dfield=DC+B*DR+B^h,
Gamma=r0^e_* (q^2-1)(1+q Dfield).
```

Gamma is positive and is a unit modulo dN. For a nonwrapping change z0 in that dummy digit at cell i, literal subtraction of the actual shifted packing formula gives

```
change C = change Z = z0 B^i,
change F = Dfield z0 B^i,
change R = -(q^2-1)(1+q Dfield) z0 B^i.         (2)
```

The source uses MF_source=MF_native+B-1 throughout. No independent R is supplied.

For the desired theorem, choose in this order:

1. Fix the adequate spatial padding h and thus E=dh.
2. Put Aminus=2^E-1, Q=3 Aminus, and let P consist of 3 and the distinct prime divisors of Aminus.
3. Increase the time padding Htime through powers of five until all original padding requirements hold and Htime>5(2Q-3).

In particular N>25d and N>2x. The set P and Q are fixed before this increase; neither depends on the new Htime. No prime dividing Aminus is 3. For every p in P,

```
B^(2h)=2^(2E)=1 mod p.                         (3)
```

Preset the upper dummy bits at the Q-1 cells

```
i_j=2h*j,  0<=j<=Q-2,
```

and set every other upper bit to zero. Initially set the lower dummy bits to zero. These changes preserve the given accepting computation. Then use the existing [Boolean five-adic subset theorem](../../1980/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md) on the lower bits in {4j:0<=j<N/5} union {1} to arrange R=dh modulo dN. It works for every baseline residue. Coinciding lower and upper bits produce the permitted digit 3.

Let Lswap=4N/5. A switch moves one preset upper bit from i_j to i_j+Lswap. The target upper bits are all zero and distinct from the source upper bits. Indeed, with i_max=2h(Q-2), the chosen height gives

```
i_max+h=h(2Q-3)<N/5,
i_max+Lswap+h<N,
i_max+Lswap+1<N.
```

Thus every spatial and temporal contribution in (2) is nonwrapping. Target cells lie beyond the old lower-control cells; in any case the bit coordinates are independent. Every digit remains between 0 and 3.

The exact five-adic valuation is

```
v5(B^Lswap-1)=v5(2^(4dN/5)-1)=v5(dN).
```

Each switch therefore preserves R=dh modulo dN. Define G=Gamma(B^Lswap-1)>0. After moving precisely the first k bits, where 0<=k<Q, the half-index is exactly

```
r_k = r_base - G sum_(j=0)^(k-1) B^(2hj).       (4)
```

Now, after the baseline and lower-bit alignment have been constructed, define s_p=v_p(G) for each p in P. These valuations are finite but need not be small or known in advance. From (3),

```
r_k = r_base - G*k mod p^(s_p+1).              (5)
```

Every digit below position s_p remains fixed. The digit at position s_p ranges bijectively over all p values as k ranges modulo p, because G/p^s_p is a unit modulo p. For each p choose the residue of k making that digit p-1. The Chinese remainder theorem gives one simultaneous representative

```
0<=k<product_(p in P) p = rad(Q) <= Q.
```

Thus the chosen prefix exists even if Aminus is not square-free. Equation (4), not an abstract independent-index operation, describes this prefix on the actual accepting word. All its full indices remain positive by the unchanged packing bounds.

More generally, the same argument works for any finite set of odd primes: replace 2h by a fixed common multiple of their orders of B, choose enough time padding for the finite grid, and prescribe any digit at the resulting position v_p(G). This only controls index digits. It does **not** by itself control a modulo those arbitrary primes, because the native evaluation base X=2^R also matters.

## 3. Passing the digit control to the exact native parameter

A base-p digit p-1 of r forces a carry in r+r. The valuation identity

```
v_p(binom(2r,r)) = sum_(j>=1) (floor(2r/p^j)-2 floor(r/p^j))
```

counts the carries, so the chosen digit implies p divides C_R. This remains true when a carry enters that digit: the first carry may have occurred earlier. We do not assume that a particular local binomial factor at the chosen digit is itself zero.

For a prime p dividing Aminus, the canonical divisibility E|R fixes X=2^R=1 modulo p. By symmetry of a full binomial row,

```
G_r(1)=(2^(2r)+C_R)/2,
a=(X+1)G_r(X)/2
  =2^(R-2)+C_R/2
  =1/4 mod p.                                  (6)
```

Division by 2 and 4 is legitimate because p is odd. Consequently

```
Delta=65/16 mod p.                              (7)
```

Neither 5 nor 13 divides Aminus: the orders of 2 at these primes are 4 and 12, whereas E is a power of five. Thus (7) is nonzero for every p dividing Aminus, and

```
gcd(Delta,2^E-1)=1.                             (8)
```

At p=3 the same prefix forces a ternary digit 2 of r. The pinned [native ternary formula](complete83_gamma_native_ternary_exclusion.md) then gives a=0 modulo 9. Hence v3(Delta)=1, v3(H)=1 and v3(m)<=1. This last bound follows from g dividing 2Delta; it does not assert that the local order modulo 3 determines the order modulo H.

The odd integers 2^E-1 and 2^E+1 are coprime. Combining (1) and (8) gives the announced exact gcd with 2^(2E)-1. Its 3-adic valuation is exactly 1, so division by 3 removes its entire 3-part. Since m divides 2Delta and (2^(2E)-1)/3 is odd, m is coprime to that quotient as well.

## 4. The full genuine-history and positive-witness interface

All prefixes preserve the same accepted input, actual computation, fixed masks and clauses. Only ignored upper bits move. Lower-bit alignment and the exact packed-index equation remain intact, so the temporal equality 2^R=B^h modulo q-1 is retained. No fixed coefficient depends on the chosen input or on the finite prime set.

The number of changed cells does not weaken the digitwise bounds. The modified compiler permits every ignored digit to be any value from 0 through 3. Its raw field coefficients are at most r0/4-2; the intended temporal word contributes at most 3. Therefore each coefficient of F is at most r0/4+1 and each coefficient of 2C+F is at most r0/4+7. For r0>=32,

```
2C+F <= (r0/4+7)(q-1)/(r0-1) < q/2.
```

The unchanged Start and End markers give 0<Z=C-W<C. With t=dN and N>2x, the original supplied slack remains positive:

```
alpha=q-C-Z-F-2dx > q/2-t >0.
```

The same low origin conditions and inverse-population identity yield popcount(R)=3dN+2 and q^2<R<q^4; the low bits still give R=3 modulo 4. These are the hypotheses already verified in [the ternary escape, Section 4](complete83_gamma_native_ternary_escape.md#4-all-original-positive-source-conditions-survive). The [half-binomial converse](pell_kernel_half_binomial42.md#6-exact-valuation-and-the-positive-converse) and the [full positive composition](../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md#6-full-positive-completeness-composition) therefore construct fresh positive first/main/strong/input/transport witnesses at this actual modified R and its exact native Y. The established normalized-strong and auxiliary-quotient changes give positive 84-operation parent witnesses, and gamma=rho+sigma gives the independent-gamma83 zero.

This is a fresh witness reconstruction after the prefix has been chosen. It does not preserve the previous numerical Pell witnesses or rely on presumed soundness of the 83-operation chart. For each fixed h there are arbitrarily large permissible time paddings, so the finite grid is compatible with every accepted input.

## 5. Consequences and the remaining obstruction

Every prime with order of 2 equal to 5^j or 2*5^j, except 3, can be included by making the legitimate spatial padding h large enough. Thus **any finite subset of that prime class can be excluded simultaneously from Delta and m on a genuine accepting history**, together with v3(m)<=1. Orders 5 and 25 give the additional examples 31, 601 and 1801; the fresh checks verify

```
2^5-1  =31,
2^25-1 =31*601*1801,
ord_31(2)=5, ord_601(2)=ord_1801(2)=25.
```

Finite factorization and the CRT are witness-construction steps in this existence proof. They are not a newly paid arithmetic circuit or a claim of efficient preprocessing. No factorization is needed to state the resulting composite gcd identity.

Primes such as 5, 7, 13 and 17 have orders 4, 3, 12 and 8 and are outside this controlled order class. Their exclusion is not asserted. Even for a fixed excluded finite set, the remaining prime factors of Delta and of ord_H(2) are not bounded. A prime divisor of H can make the order contain other primes, and only its intersection with 2Delta contributes to g. The theorem does not control that intersection outside the stated set.

Increasing h changes the constructed history. There is no compactness or diagonal step producing one finite history which avoids an infinite set of primes, and no inference from arbitrarily large finite exclusions to a bound on m. In particular no false-input alias, no occurrence of the H-1 or H-3 power tests, and no resolution of independent-gamma83 is claimed.

## 6. Fresh evidence and replay

The [fresh helper](complete83_gamma_native_finite_prime_avoidance.py) authenticates twelve predecessor source/proof files as inert bytes. Its [receipt](complete83_gamma_native_finite_prime_avoidance.json) records nine independently enumerated prime orders, both exact factorizations for E=5 and 25, fifteen native plus-factor samples, eight combined native-formula samples, two finite-grid size calculations, twenty-four simultaneous prefix/CRT congruence samples and sixty-four independent finite geometric-sum checks. Native evaluations use exact integer binomial coefficients; central divisibility is independently compared with prime-field digit products.

The CRT samples use synthetic positive Gamma values and bounded modular data. The grid records describe numerical geometries; they do not materialize their enormous arrays of bits. The formula indices are not claimed to satisfy all compiler constraints. **No full accepting history or full positive Pell tuple is numerically materialized here.** The genuine-history assertion is the unrestricted proof in Sections 1–4 with the authenticated compiler and converse.

The helper executes no predecessor code, imports no historical builder, changes no frozen artifact, and uses explicit exceptions under optimized Python. JSON receipts reject duplicate/nonfinite values and compare types recursively. From any working directory use

```
python3 complete83_gamma_native_finite_prime_avoidance.py --root ABS_WIP --expect ABS_JSON
python3 -O complete83_gamma_native_finite_prime_avoidance.py --root ABS_WIP --expect ABS_JSON
```

Use --output FILE to write the deterministic receipt. Fresh normal and optimized exact receipt replays from / passed.
