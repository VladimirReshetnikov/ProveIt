# Native small-prime digit rules and a parity-dependent history filter

There is a genuine-history extension of the previous finite-prime filter: **if the fixed compiler has an even number of window selectors and an odd tile-alphabet size, every accepted positive input has genuine accepting witnesses satisfying the stronger filter below**. In particular 7 does not divide Delta. Fix an adequate canonical spatial padding h, then:

```
E=dh,
gcd(Delta, 2^(6E)-1)=3,
gcd(Delta, (2^(6E)-1)/9)=1,
v3(m)<=1.
```

The compiler parity is a hypothesis about its actual fixed layout. This note does not assert that every compiler has this parity or that changing its alphabet preserves a particular instantiated compiler.

For the other native bases at 5, 7, 13 and 17, an exact digit recurrence proves a different result. A finite prescribed block of base-p digits, together with the fixed scalar congruences, cannot alone force a safe residue of the native binomial formula when higher digits remain unrestricted. Every value of a modulo p still occurs among formula indices satisfying those restrictions. These formula extensions are **not claimed to be actual histories**: they need not satisfy the population, mask, packing-size or computational constraints. Thus this second theorem delimits a particular digit-only proof route; it neither constructs false-input witnesses nor excludes a stronger history-dependent argument.

No circuit changes. The ordinary-input language of [independent-gamma83](complete83_independent_gamma_scout.md) remains unresolved.

## 1. The actual compiler fixes the evaluation bases

Use the notation of the [modified compiler](complete75_half_binomial_compiler.md): inner radix r0=2^b, cell radix B=2^d, q=B^N, J=(q-1)/(B-1), native masks MC and MF, and the source coefficient MF_source=MF+B-1. The current fixed recipe has b,d,h,Htime and N powers of five, b>=5, N=h Htime. Its canonical packed index satisfies

```
R=dh mod dN,
R=(q^2-Z-qF)(q^2-1)+(MC+q*MF_source)*J.
```

At the origin the actual content word has Start selector 0, so its unit r0-digit is 1. The End marker has exponent b+2dx>=b. Consequently Z=C-W=1 modulo r0. The literal mask formula from [the compiler-order filters, Section 1](complete75_gamma87_compiler_order_filters.md#1-the-parameter-and-the-actual-compilers-fixed-residues) is

```
MC=B-1-sum_(e in positions,e!=1) r0^e -2r0^e_*.
```

The summation contains the exponent 0, and e_*>1, so MC=-2 modulo r0. Also q=0 and J=1 modulo r0. Substitution into the actual packing equation proves

```
R=Z+MC=-1 mod 2^b.                              (1)
```

This strengthens the previously retained R=3 modulo 4; it does not prescribe an independent index. All permitted dummy switches preserve the underlying origin conditions.

Let k be the window-selector count and a_T the tile-alphabet size. The authenticated compiler-order filter proves the following exact table for every canonical history (N is odd):

| Fixed compiler class | R modulo 3 |
| --- | ---: |
| k odd | 2 |
| k even, a_T even | 1 |
| k even, a_T odd | 0 |

Together with (1), this fixes X=2^R in the following fields:

| p | R modulo 3 = 0 | R modulo 3 = 1 | R modulo 3 = 2 |
| --- | ---: | ---: | ---: |
| 5 | 3 | 3 | 3 |
| 7 | 1 | 2 | 4 |
| 13 | 8 | 11 | 7 |
| 17 | 9 | 9 | 9 |

The orders of 2 are respectively 4, 3, 12 and 8. For 13 the combined residues of R modulo 12 are 3, 7 and 11; for 17, (1) gives R=7 modulo 8. The base X cannot be independently selected by a high dummy switch.

## 2. A two-state digit recurrence

For an odd prime p, fix x in F_p distinct from 0. Define

```
C(r)=binom(2r,r) mod p,
G(r)=sum_(j=0)^r binom(2r,r+j)*x^j mod p.
```

Write r=pk+d with 0<=d<p. If 2d<p, put

```
c_d=binom(2d,d), L_d=(1+x)^(2d),
U_d=sum_(j=d)^(2d) binom(2d,j)*x^j.
```

Then

```
C(r)=c_d*C(k),
G(r)=x^(-d)*(L_d*G(k)+(U_d-L_d)*C(k)).           (2)
```

If 2d>=p, then

```
C(r)=0,
G(r)=x^(-d)*(1+x)^(2d-p)*((1+x)*G(k)-C(k)).     (3)
```

Here C(0)=G(0)=1. These are identities in the prime field, with no approximation or assumption about the lower digits.

For completeness, Lucas splitting of a term in the full binomial row uses the two digits of 2r. In the first case, high row indices greater than k admit every low index; at high index k only low indices at least d are admitted. Their weighted sums are respectively x^k(G(k)-C(k)) and x^k C(k). This gives (2). In the second case the low row length is 2d-p<d, so the high index must be at least k+1. Pascal's identity gives its weighted sum

```
sum_(j>=k+1) binom(2k+1,j)*x^j
  =x^k*((1+x)*G(k)-C(k)),
```

which proves (3). Lucas also gives the stated central coefficient in each case.

Suppose now x!=-1 and put z=(1+x)^2/x, a nonzero field element. The coefficient of G(k) in **both** (2) and (3) is z^d: in (3) use (1+x)^(p-1)=1. In particular, once C(k)=0,

```
C(pk+d)=0,
G(pk+d)=z^d*G(k),
T(pk+d)=T(k),  where T(r)=z^(-r)*G(r).           (4)
```

The last equality uses z^p=z. A zero central coefficient in a higher prefix persists on appending any lower digits, and its normalized sum T remains fixed. A carry appearing in a later lower digit cannot reset that state.

At x=1, symmetry gives G(r)=(4^r+C(r))/2. Thus C(r)=0 forces the single normalized state T(r)=1/2. At the other bases in Section 1, the normalized state has a very different range.

## 3. Exact full-state certificates and the digit-only limitation

For each of the following (p,x), the fresh receipt supplies p explicit nonnegative prefixes t, one for each lambda in F_p, and checks their entire binomial rows:

```
C(t)=0, T(t)=lambda.
```

| p | x | Number of prefixes | Largest prefix |
| --- | ---: | ---: | ---: |
| 5 | 3 | 5 | 158 |
| 7 | 2 | 7 | 410 |
| 7 | 4 | 7 | 410 |
| 13 | 8 | 13 | 2412 |
| 13 | 11 | 13 | 1073 |
| 13 | 7 | 13 | 1073 |
| 17 | 9 | 17 | 1505 |

These 75 complete finite certificates, together with (4), prove an unrestricted statement; they are not an extrapolation from a sample of long indices.

**Precise extension theorem.** Fix one row of this table. Let M be any positive integer coprime to p and divisible by p-1. Fix a residue r0 modulo M such that 2^(2r0+1)=x modulo p. Fix any ell>=0 and any low-digit prescription r=v modulo p^ell. For every desired A in F_p there are infinitely many nonnegative integers r such that

```
r=r0 mod M, r=v mod p^ell,
C(r)=0,
2^(2r+1)=x mod p,
(1+x)*G(r)/2=A mod p.                           (5)
```

To prove this, select the certified high prefix t with

```
T(t)=2A*(1+x)^(-1)*z^(-r0).
```

Choose arbitrarily large L with p^L>=M*p^ell. In the prefix interval

```
t*p^L <= r < (t+1)*p^L
```

the Chinese remainder theorem supplies a suffix w=r-t*p^L in [0,M*p^ell) satisfying the two congruences. The digits of r are exactly the high prefix t followed by L lower digits (including leading zeroes in the suffix). Equation (4) therefore gives C(r)=0 and T(r)=T(t). Because M contains p-1, both z^r=z^r0 and 2^(2r+1)=x remain fixed. This proves (5). The positive prefixes and arbitrarily large L give infinitely many distinct r.

An arbitrary consistent finite prescription of intermediate digits is covered by completing it to one lower residue v modulo p^ell. Crucially, the construction **prefixes a new high block and appends the prescribed lower suffix**. It does not assume that changing a high prefix leaves an earlier recurrence state unchanged. The recurrence is evaluated from high digits to low digits; even if the prescribed lower suffix already includes a carry, it cannot undo the higher prefix's C=0 state.

The scalar congruences (1), R modulo 3 and R=dh modulo dN can all be incorporated in this statement, provided the requested digit prescription is consistent with them. Put their prime-to-p parts, together with p-1, into M. If p=5, incorporate the required power-of-five part into the lower residue v; for the other displayed primes the canonical dN is coprime to p. Any added compatible residue modulo p-1 can be fixed as well. Converting R=2r+1 causes no difficulty: p is odd, and (1) is r=-1 modulo 2^(b-1).

In particular (5) admits A=-1 and A=-3, for which Delta=(A+1)(A+3)=0, as well as A=0, for which Delta=3 is nonzero at these primes. Thus those scalar congruences and an arbitrarily long finite base-p prescription do not themselves imply p does not divide Delta.

This is **not** a theorem that any such prefix or index can be realized by the compiler. The proof takes unbounded higher prefixes. It does not retain a fixed q's interval q^2<R<q^4, popcount(R)=3dN+2, the native masks, the word's actual convolution, or a genuine computation. A fixed finite history has a finite length; prescribing all its digits is outside the unrestricted-tail premise. The theorem leaves open a digit method that uses those additional history constraints or chooses a residue based on the actual higher state.

## 4. A genuine p=7 extension in one fixed compiler class

Now assume k is even and a_T is odd. The actual table of Section 1 gives R=0 modulo 3 on every canonical history, and therefore X=1 modulo 7. This conclusion is independent of the dummy choices.

Fix any accepted positive input, choose an adequate canonical spatial padding h first, and put E=dh. Preserve the order of choices in [the finite-prime theorem](complete83_gamma_native_finite_prime_avoidance.md): define

```
Aminus=2^(3E)-1,
Q=3*Aminus,
P={3} union {prime divisors of Aminus}.
```

These are fixed before time padding is increased. Since E is a power of five, Aminus is not divisible by 3 and is divisible by 7. Choose a pure-five time padding Htime satisfying all original requirements and

```
Htime>5*(6Q-11), N=h*Htime, Lswap=4N/5.
```

Preset the upper dummy bits at i_j=6h*j for 0<=j<=Q-2. Align the independent lower bits to the original congruence R=dh modulo dN. For i_max=6h(Q-2),

```
i_max+h=h*(6Q-11)<N/5,
i_max+Lswap+h<N.
```

Thus every source, destination, and shifted field contribution is nonwrapping, exactly as in the prior proof. The enlarged spacing is necessary: the old spacing 2h need not give a return modulo 7. Here

```
B^(6h)=2^(6E)=1 modulo every p in P.
```

Move a prefix of the preset upper bits from i_j to i_j+Lswap. With the actual positive Gamma from that proof, set Gswitch=Gamma*(B^Lswap-1). The exact half-index is

```
r_k=r_base-Gswitch*sum_(j<k) B^(6hj), 0<=k<Q.
```

Every move preserves the five-adic alignment. After the baseline is fixed, put s_p=v_p(Gswitch). The displayed sum is k modulo p. Multiplication by Gswitch, whose p-adic valuation is s_p, therefore gives r_k=r_base-Gswitch*k modulo p^(s_p+1). A CRT representative k<rad(Q)<=Q simultaneously makes the s_p-th base-p digit of r_k equal to p-1 for every p in P. Each such digit forces a central-binomial carry.

The parity class fixes R=0 modulo 3, while canonical alignment gives E|R and gcd(E,3)=1. Thus 3E divides R and R/(3E) is odd. Consequently every canonical history, before any new switches, satisfies

```
2^(3E)+1 divides 2^R+1 and divides a,
Delta=3 mod (2^(3E)+1),
gcd(Delta,2^(3E)+1)=3.
```

Here v3(2^(3E)+1)=1+v3(3E)=2. In particular a=0 modulo 9 and v3(Delta)=1 already follow for every such history; no digit prescription is needed for this last assertion.

For each prime p dividing Aminus, the actual divisibility 3E|R fixes X=1 modulo p. The switch forces C(r)=0, and symmetry gives a=1/4, Delta=65/16 modulo p. Neither 5 nor 13 divides Aminus, because their orders 4 and 12 cannot divide the odd integer 3E. Therefore Delta is nonzero at every prime dividing Aminus and gcd(Delta,Aminus)=1. The prime 7 is among them, with the particularly simple values

```
a=G(r)=(2^(R-1)+C(r))/2=1/4=2 mod7,
Delta=(a+1)(a+3)=65/16=1 mod7.                  (6)
```

This is why p=7 succeeds in this compiler class even though ord_7(2)=3 does not divide 2E. It uses the actual mask-imposed R modulo 3, not a freely chosen base. The same argument also covers all prime divisors of 2^(3E)-1.

All digits remain 0 through 3. The prior digitwise bound 2C+F<q/2, unchanged Start and End, N>2x, and the same actual population and temporal congruence give the original positive slack and a fresh positive 84-parent extension at the modified R. The independent-gamma forward map then supplies its positive zero. These are exactly the authenticated fresh-converse interfaces used in the preceding finite-prime theorem; no old Pell tuple is retained.

The two factors 2^(3E)-1 and 2^(3E)+1 are coprime, so the preceding identities prove gcd(Delta,2^(6E)-1)=3. The composite 2^(6E)-1 has exact 3-adic valuation 2; dividing by **9**, rather than by 3, removes its entire 3-part. Thus gcd(Delta,(2^(6E)-1)/9)=1. Since m divides 2Delta, it is coprime to this odd quotient, and v3(m)<=1. In particular 7 does not divide m.

As h increases legitimately through powers of five, any finite set of primes other than 3 whose orders divide some 6*5^j can be excluded simultaneously by this construction. The fresh checks give

```
2^15-1 = 7*31*151,    ord_151(2)=15,
2^15+1 = 9*11*331,    ord_331(2)=30.
```

This includes new examples 7, 151 and 331 beyond the preceding power-five order classes. It is still a finite-history existence statement for each fixed finite set; there is no infinite diagonal or compactness conclusion. For the other two compiler parity classes, X is 2 or 4 modulo 7; equation (6) is unavailable and Section 3's formula limitation applies. This note makes no compiler-padding claim that would remove the parity hypothesis.

## 5. Evidence, reproducibility and remaining boundary

The [fresh standard-library helper](complete83_gamma_small_prime_digit_rules.py) authenticates six predecessor files as inert bytes. It neither imports nor executes predecessor code. Its [receipt](complete83_gamma_small_prime_digit_rules.json) saves all 75 carry-prefix certificates and independent whole-integer-binomial-row evaluations. It additionally records 4,598 exact recurrence comparisons, 919 digit-append checks, 75 explicit synthetic congruence extensions covering every target residue in the seven nontrivial rows, 127 single-carry formula samples at 7, two enlarged grid geometries, 27 synthetic leading-digit congruence checks, three exact prime/order checks and the two displayed factorizations.

The formula samples, CRT values and geometries are bounded corroboration. They are not materialized accepting histories or full positive Pell tuples. The genuine-history result is the unrestricted argument in Section 4 with its pinned compiler and converse dependencies; the all-state extension result follows from the complete finite prefix certificates and Section 3's proof.

Receipts reject duplicate/nonfinite JSON and compare recursive types exactly. Explicit exceptions remain enabled under optimized Python. From any directory run

```
python3 complete83_gamma_small_prime_digit_rules.py --root ABS_WIP --expect ABS_JSON
python3 -O complete83_gamma_small_prime_digit_rules.py --root ABS_WIP --expect ABS_JSON
```

Use --output FILE to emit the deterministic receipt. Fresh normal and optimized exact receipt replays from / passed. This packet establishes no new operation bound, no full bound on m, and no occurrence of the old H-1/H-3 order tests. In particular finite control of these prime factors does not control contributions from the remaining factors of ord_H(2).
