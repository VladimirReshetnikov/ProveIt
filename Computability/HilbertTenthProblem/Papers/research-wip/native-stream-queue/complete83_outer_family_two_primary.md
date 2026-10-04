# Eventual two-primary success in the actual non-dyadic outer family

For the frozen actual-compiler outer family, the two-primary part of the cubed-scale condition holds for **every sufficiently large family parameter**. The threshold below is explicit and depends only on the fixed compiler constants. The remaining condition is entirely at the odd prime divisors of q; no member is proved to pass those conditions, no full positive zero is asserted, and there is no universal83 conclusion.

This note changes none of the83 source rows or18 supplied witnesses. It uses the outer-family construction as an inherited theorem and proves the new divisibility statement by ordinary integer digit arithmetic. The helper corroborates the proof on bounded relaxed scalar layouts without running a compiler, any predecessor program, or a Pell computation.

## 1. Family and fixed threshold

Retain the actual fixed constants of `complete83_nondyadic_outer_family.md`:

```
B=2^d, d>=25, b>=5,
K=DC+B*DR>B,
0<MC<B−1, 0<MF0<B−1, MF=MF0+B−1,
MC=2 mod4.
```

The original coefficient recipe has DC>0 and DR>=1, giving the stated lower bound K>B. This matters: the argument does not extend indiscriminately to a synthetic K=1.

For positive n=1 modulo4 let D=dn, Q=B^n. The frozen family chooses one of

```
plus:  q=Q(Q+1)/2,
minus: q=Q(2Q−1),
```

with J=(q−1)/(B−1), a constructed z satisfying1<=z<=4d and z=1 modulo4, F=Kz, C=Z=z, W=0, and

```
R=q^4−Fq^3−(z+1)q^2+Fq+z+S,
S=(MC+q*MF)J,
u>=2D+b, R>u, X=2^R−2^u.
```

Here S denotes the mask contribution only; it is unrelated to the auxiliary Pell root. The family theorem supplies R=3 modulo4, 0<R<q^4, positivity of all outer slacks, and q(q−1)|X. We retain all its domain restrictions and construction of the ordinary input; no arbitrary-input family is asserted.

Define the fixed integers

```
Astar=64(4dK+4d+1),
ell=bitlength(Astar), so Astar<2^ell,
Nstar=3ell+5.                                     (1)
```

**Theorem.** Every member of the frozen family with n>=Nstar satisfies

```
v2(M_r(X))=popcount(r)>=3v2(q)+1,
r=(R−1)/2,
2^(3v2(q)) divides Y=M_r(X)/2.                    (2)
```

In particular the2-primary part of q³|Y is automatic on this infinite tail. The family still requires n=1 modulo4. The least permitted n at leastNstar and all its successors by4 meet this theorem.

The outer-family bounds K+2<4B^(5/4) and64d<B^(3/4) also imply

```
Astar<256d(K+2)<1024d B^(5/4)<16B²<B³.
```

Thus ell<=3d, and Q>Astar already holds for n>=5. The theorem retains the explicit threshold(1); this auxiliary estimate makes no additional claim about which smaller members pass.

## 2. Exact low digits and absence of denominator resonances

For n>=5, q is divisible by B^(n−1), and the extra factor in J is1 modulo B^(n−1). More precisely,

```
J = ((Q−1)/(B−1))*(Q/2+1)       in the plus shape,
J = ((Q−1)/(B−1))*(2Q+1)        in the minus shape.
```

Therefore

```
R = z+MC*(1+B+...+B^(n−2)) mod B^(n−1).           (3)
```

Indeed all q-dependent terms vanish at that modulus, leaving z+MCJ. We do not need to reduce modulo the slightly larger power2^(D−1).

Since z<=4d and d>=25, z+5<B. Adding z to the repeated MC word can affect its first two B-digits only: MC+z<2B, so the first carry is at most1, and the next digit is MC or MC+1, both at mostB−1. Thus the digits of R at B-positions

```
2,3,...,n−2                                      (4)
```

are exactly MC. There are n−3 such unchanged digits, each with at least one set bit.

The same argument applied to z+1 and z+5 shows that the second B-digit of R+1 and R+5 lies between MC and MC+1. It is nonzero and smaller thanB. Consequently

```
v2(R+1)<2d,  v2(R+5)<2d.                         (5)
```

Set p=popcount(r), k=v2(r+1), h2=v2(r−1), j=v2(r+3), and alpha=v2(X). Since R>u,

```
alpha=u>=2D+b,
k=v2(R+1)−1<2d,
j=v2(R+5)−1<2d.                                 (6)
```

The adjacent binomial ratios and v2(binomial(2r,r))=popcount(r) give the four coefficient valuations

```
p, p−k, p+h2−k, p+h2−k−j.                        (7)
```

After multiplication by1,X,X²,X³, the last three valuations are strictly greater than p, by(6), h2>=1 and n>=5. Thus the central term is uniquely smallest. This directly excludes both cancellation branches of the separate two-adic stratification for this family tail; no freely chosen unit root is used.

For completeness the higher terms also cannot change the exact valuation. Since q<2Q² and r=(R−1)/2<q^4/2, we have r<8Q^8 and hence p<=8D+3. On the other hand alpha>=2D+b with b>=5 gives4alpha>=8D+20. Every term C_i X^i for i>=4 has valuation at least4alpha>p. Therefore

```
v2(M_r(X))=p                                    (8)
```

for every family member with n>=5. This statement is exact, not only modulo the target power.

## 3. Three high complement digits in the minus shape

The mask satisfies

```
0<S<(1+2q)(q−1)<2q².                             (9)
```

This follows from0<MC<B−1,0<MF<2(B−1) and J=(q−1)/(B−1). Put F=Kz. We have F>=4 and F<=4dK. Once Q>Astar, the following expansion is valid without any assumption about the unknown low digits of S:

```
R=16Q^8−32Q^7+(24−8F)Q^6+(12F−8)Q^5
  −(6F+4z+3)Q^4+(F+4z+4)Q^3
  +(2F−z−1)Q²−FQ+z+S.                             (10)
```

After division by Q^4, let epsilon be the integer carry from the terms below Q^4. The absolute value of their polynomial part, excluding S, is at most

```
(4F+6z+5)/Q < Astar/Q <1.
```

Also S/Q^4<8 because q<2Q². Hence

```
−1<=epsilon<=8.                                  (11)
```

The Q^4 coefficient is negative, so normalization borrows1 from Q^5. Its resulting coefficient12F−9 is positive and less thanQ. Independently Q^6 is negative, borrowing from Q^7, which then borrows from Q^8. Thus the three exact base-Q digits at positions4,6,7 are

```
Q−a4,  Q−a6,  Q−a7,
a4=6F+4z+3−epsilon,
a6=8F−24,
a7=33.                                          (12)
```

All three deficits satisfy1<=a_i<Astar<Q. Every other high coefficient after these carries is also between0 andQ−1: they are12F−9 at position5 and15 at position8. This closes the carry accounting; there is no assumed absence of borrowing in S itself.

## 4. Three high complement digits in the plus shape

Multiplication by16 does not change population count. Clearing the dyadic denominators in q=(Q²+Q)/2 gives

```
16R=Q^8+4Q^7+(6−2F)Q^6+(4−6F)Q^5
    −(6F+4z+3)Q^4−(2F+8z+8)Q^3
    +(8F−4z−4)Q²+8FQ+16z+16S.                       (13)
```

The polynomial part below Q^4 has absolute value after division by Q^4 at most

```
(18F+28z+12)/Q < Astar/Q <1.
```

Moreover16S/Q^4<8(1+1/Q)²<9 for Q>=32. Therefore its integer carry epsilon satisfies

```
−1<=epsilon<=9.                                  (14)
```

Normalizing the negative coefficients at positions4,5,6 produces exactly

```
Q−a4,  Q−a5,  Q−a6,
a4=6F+4z+3−epsilon,
a5=6F−3,
a6=2F−5.                                        (15)
```

Again1<=a_i<Astar<Q. The carries leave the positive digits3 at position7 and1 at position8, so no further carry changes these three complement blocks.

## 5. Disjoint population lower bound

For any1<=a<Q=2^D,

```
popcount(Q−a)=D−popcount(a−1).                   (16)
```

All deficits in(12),(15) are less than Astar<2^ell. Each high complement digit thus contains at leastD−ell set bits. Together the three high digits contribute at least3D−3ell.

The n−3 low repeated MC digits from(4) are disjoint from these high blocks. In the minus shape they lie below bitD, while the lowest high block starts at4D. In the plus shape we count16R, so those low bits shift left by4; their upper boundary is(d(n−1)+4)<=D since d>=25. They are still disjoint from all high blocks. Therefore both shapes satisfy

```
popcount(R)>=3D−3ell+(n−3).
```

Since R is odd, subtracting1 clears exactly its last bit and division by2 preserves population count. Hence

```
popcount(r)>=3D−3ell+n−4.                        (17)
```

If n>=3ell+5, equation(17) is at least3D+1. Also D=dn>=ell, so Q>=2^ell>Astar and Q>=32, justifying every high-digit estimate used above. The exact two-adic exponent of q is D−1 in the plus shape and D in the minus shape. Thus

```
popcount(r)>=3D+1>=3v2(q)+1.
```

Together with(8), this proves(2).

## 6. Remaining condition, evidence, and scope

The full scale condition on this infinite tail is now equivalent to its odd-primary part. For each odd p^a || q, the preceding odd-prime note gives the exact test

```
v_p(C_0+C_1X+C_2X²)>=3a.
```

It retains the two exceptional local cancellation branches and the actual coupling X=2^R−2^u. Neither the present population proof nor local root lifting establishes those odd-prime conditions. Factoring the growing odd factors and checking finitely many cases would likewise not prove all-size success. No completed source zero or language counterexample is asserted.

The fresh companion authenticates the unchanged83 receipt and the frozen outer-family, even-radix and odd-prime notes as inert bytes. It verifies13 literal outer rows, independently expands(10),(13) as exact sparse polynomials, and checks(7) against499 small exact binomial calculations. Its64 bounded digit cases use explicitly synthetic relaxed coefficient/mask data at d=25;32 lie above the uniform threshold. They verify every claimed complement digit, carry range, repeated MC block and population bound. The largest materialized packed index has25,004 bits. No X=2^R, half-binomial value Y, actual compiled table, or Pell witness is materialized. These tests corroborate the proof, not actual universal programs.

No predecessor or supplied helper is executed or imported; the fresh standard-library code is the only executed program. No repository file is changed. The current source ledger and degree remain inherited, not re-audited by this proof packet. The relevant prior prose was read in full; the separate two-adic cubic draft was also read as context, but its results are not needed as an extra unproved premise here because the adjacent valuations and unique-minimum argument are supplied explicitly.


**Correction remark1 (retained pre-freeze errors).** The author's first draft omitted the constant +z from the polynomial for R and the corresponding +16z from16R. Subtracting either erroneous displayed right side from the actual source gives respectively z or16z, which is nonzero since z>0. The formal polynomial checker initially repeated this omission, although the digit tests already evaluated the literal correct source expression. Equations(10),(13), the two formal expansions, and their conservative tail bounds now include those constants. The same draft described the extra factors Q/2+1 and2Q+1 in J as divisible by B^(n−1); each is actually1 modulo that modulus. Only its nonconstant part is divisible. Section2 now states that corrected residue. These errors and their explicit failures are retained here rather than silently removed.

The companion JSON pins all dependencies and the helper. Fresh normal and optimized-Python exact receipt checks passed from / before freeze. Root and Aristotle independently challenge the new carry and population argument; any final review remains a separate artifact.
