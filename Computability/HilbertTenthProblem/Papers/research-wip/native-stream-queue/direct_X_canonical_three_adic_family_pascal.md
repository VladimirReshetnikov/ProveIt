# Exact canonical three-adic scales and their compiler-radix obstruction

For every integer e>=1, the canonical half-binomial at R=2*3^e-3 has
**v3(Y_R)=e-1**. Consequently an infinite family of even nondyadic q
satisfies the complete scalar cubic-scale requirement and the retained
index-size bounds. Root's separate arithmetic observation, checked below,
then rules out this entire q family on every inherited original compiler
slice: its required repunit equation is impossible. No full compiler zero
or universal83 result follows.

This continues the corrected base-prime scope of the committed
`direct_X_short_period_lucas_obstruction_pascal.md` together with its
mandatory `direct_X_short_period_lucas_obstruction_v2_pascal.md` correction.
Their SHA256 pins are respectively
`726c18d0d0fbba1d04bde35003093f25028e8556c299cf7e868e32d1dbc1f29b`
and `f8b4ac55b282857cfbcba25a53913f79aabec24ab704e63f87ce283be3c9916c`.
Both committed notes were read in full as inert text. Their exceptional
base prime p=3 in the (h,j)=(1,2) branch is now resolved to exact depth.
The general Lucas recurrence is not reproved or claimed as new here.

## 1. An exact expansion at X=-1

For r>=1 let

```
H_r(X)=sum(j=0..r) binom(2r,r+j)*X^j.
```

The following polynomial identity over the integers is useful:

```
H_r(X)=sum(j=0..r) A_j*(1+X)^j,
A_j=binom(2r-j-1,r-1).                            (1)
```

Here A_0=binom(2r,r)/2. For a direct proof, the defining coefficients
of H satisfy their adjacent-binomial recurrence. Summing it gives

```
X(1+X)H'_r(X)+r(1-X)H_r(X)=r*binom(2r,r).        (2)
```

Writing H_r(-1+t)=sum A_j*t^j, its constant equation gives
2r*A_0=r*binom(2r,r), and its subsequent equations give

```
(2r-j)A_j=(r-j+1)A_(j-1), 1<=j<=r.              (3)
```

The stated binomial formula satisfies these equations. The denominators
2r-j are nonzero rational integers, so the recurrence uniquely determines
the coefficients, establishing (1) over Q and hence over Z. This is a
proof of an integer polynomial identity, not a division inside a source
circuit. No inference about p-adic units is made from these denominators.

## 2. Exact valuation at the exceptional prime

Put P=3^e, r=P-2, R=2P-3, X=2^R and Y_R=H_r(X)/2. Then r>=1, R>=3
and Y_R is a positive integer. The exact coefficient valuations in (1) are

```
v3(A_j)=e-v3((j+2)(j+3)(j+4)), 0<=j<=P-2.        (4)
```

To prove this, first Legendre's factorial formula gives
`v3(binom(2P-4,P-2))=e-1`. In its floor sum, the term for 3 is zero;
each power 3^a with 2<=a<=e contributes one, and all later terms vanish.
Division by 2 does not change this valuation, so v3(A_0)=e-1.

Iterating (3), the numerator factors have the form P-d for
2<=d<=j+1<P. Their valuations are v3(d). Denominator factors have the
form 2P-d for 5<=d<=j+4<=P+2<2P. If d!=P then v3(d)<e and again
v3(2P-d)=v3(d); if d=P both valuations equal e. Empty products are
interpreted as 1. It follows that

```
v3(A_j)-v3(A_0)
  =v3((j+1)!)-v3((j+4)!/4!)
  =1-v3((j+2)(j+3)(j+4)),                        (5)
```

which proves (4), including e=1 and j=0.

For these indices v3(R)=1. The elementary odd-exponent lifting formula
therefore gives

```
v3(1+2^R)=v3(1+2)+v3(R)=2.                      (6)
```

The constant term in (1) has valuation e-1. For j>=1, exactly one of
j+2,j+3,j+4 is divisible by 3, and thus

```
v3((j+2)(j+3)(j+4)) <= log_3(j+4) < 2j+1.
```

The strict inequality follows from `j+4<3^(2j+1)` for j>=1, proved at
j=1 and preserved on incrementing j. Combining this bound, (4) and (6)
shows every nonconstant term of (1) has valuation strictly greater than
e-1. The uniquely least-valued term cannot cancel. Since 2 is a 3-adic
unit, this proves the all-size theorem

```
v3(Y_(2*3^e-3))=e-1, for every e>=1.             (7)
```

This treats the full canonical sum, not just its central coefficient.
Unlike the earlier p>=5 counterexamples, the constant term is now proved
to be uniquely minimal after expansion about -1.

## 3. An infinite scalar cubic-scale family

For every even integer k>=2 set

```
q=2*3^k,
e=3k+2,
R=2*3^e-3=(9/4)q^3-3,
X=2^R.                                          (8)
```

Then q>=18 is even nondyadic, R=3 modulo 4, and (7) gives
`v3(Y_R)=3k+1>=3k`. The binary part also follows exactly. For any odd
R=2r+1>=3, the central term of H_r(2^R)/2 has binary valuation
`pc(r)-1`, whereas every other term has valuation at least R-1. Since
pc(r)-1<R-1, Legendre's identity for the central binomial gives

```
v2(Y_R)=pc(r)-1=pc(R)-2.                         (9)
```

Here pc is binary population. In (8), e is even, so 3^e=1 modulo 8
and R=-1 modulo 16. Also R>15, giving pc(R)>=5. Thus v2(Y_R)>=3, and

```
q^3 divides Y_R,           q does not divide X.   (10)
```

The retained numerical outer interval also holds:

```
(2q-1)(q^2-1)<R<q^3(q-1).                       (11)
```

For the lower endpoint, the exact difference is
`q^3/4+q^2+2q-4>0`. For the upper endpoint, it is
`q^3*(q-13/4)+3>0`. Both are positive for q>=18.
These are scalar canonical data; no F,Z,positive slack, transport or
compiler repunit has been supplied. In fact the next section proves
that the last omission cannot be repaired in this family.

## 4. Root's all-compiler repunit obstruction

Root found the following congruence conflict and its literal recipe
binding. I independently read the cited source definitions and verified
the small scalar residue identities. Root's separate frozen evidence is
`direct_X_single_prime_radix_root.json`, SHA256
`2caf1521fa8c13d5204c9c8ed951a529e37b3166d8057af0fbfb5b580c344378`,
read in full as inert metadata. If 25 divides d and B=2^d, there
is **no integer k>=0** such that

```
B-1 divides 2*3^k-1.                             (12)
```

Indeed `2^25-1=31*601*1801`, so both 31 and 601 divide B-1. The exact
orders and the residues needed here are

| Modulus | Order of 3 | Power giving inverse of 2 | Proper-divisor checks |
|---|---:|---:|---|
|31|30|3^6=16|3^15=30, 3^10=25, 3^6=16|
|601|75|3^42=301|3^25=24, 3^15=32|

Also 3^30=1 modulo 31 and 3^75=1 modulo 601. The listed proper-prime-divisor
checks establish the exact orders. This argument needs only the unit
orders, not an assumption or proof that the moduli are prime.
Equation (12) would consequently force

```
k=6 modulo 30,      k=42 modulo 75.
```

Modulo 15 these become k=6 and k=12, a contradiction.

This covers every inherited original modified75 compiler used by direct-X83.
The actual modified75 recipe keeps b,L,d powers of 5, requires 2^b>=16,
and inherits L from the complete76 layout. Hence 5 divides b. In that
layout the native positions include Start 0 and End 1, so Emax>=1;
`g=T2+Emax+1`, with T2>=0, and `L>g+Emax>=3`. Since L is a power of 5,
5 divides L. Therefore 25 divides d=bL. The actual source retains
`q=(B-1)J+1`; (12) forbids every q=2*3^k, independently of the other
coordinates, ordinary input, or any Pell completion.

**Review remark 1 (kernel scale does not give a compiler zero).** The
inference that the infinite family (8)--(11) extends to a positive zero
of the inherited direct-X83 compiler is false: its repunit equation is
impossible by (12). The smaller numerical choice d=5, B=32 can admit
k=6 modulo 30, but it violates the inherited requirement 25|d and is
not an authentic compiler instance. No old failed inference is silently
promoted by the successful cubic-scale theorem.

## 5. Remaining scope and evidence

**Open question 1.** Exact higher valuations at other exceptional primes
or an unbounded quotient h might still support a different radix family.
The two-state Lucas theory and its limitations remain as previously
recorded. Neither the original short-period q nor general canonical
no-wrap direct-X83 soundness is decided here. The family in (8) is
excluded at the repunit stage on every inherited original slice.

The new checker uses only independently handwritten scalar formulas:
coefficient comparisons for (1), exact modular evaluation of (1)'s
original binomial definition, finite checks of (4), and the small modular
order identities in Section 4. It never evaluates a saved source array,
imports a predecessor helper, or materializes a native tuple. Its finite
controls are not proofs of compiler completeness. All scientific code is
new and is run only before its own freeze; no repository or Git mutation
occurs.

The receipt pins both committed Lucas notes, the canonical repair interface,
and exact read spans in `complete75_half_binomial_compiler.md` (1--65)
and `FIXED_RAW_UNIVERSAL_76_PROOF.md` (1--165). The source facts used for
25|d occur in their first sections; later historical kernel claims are
not recertified. No arithmetic gate, witness or universal bound changes.

Pre-freeze normal and optimized (`-O`) runs produced byte-identical final
receipts: 350 exact polynomial-coefficient comparisons, 3272 coefficient
valuation checks, seven direct canonical modular sums (e=1 through 7),
six scalar-family size/population controls, and the two exact unit-order
certificates. These remain bounded scalar evidence at the scope above.
The new helper's SHA256 is
`f3fcc83f78ad0aaad9bcfdbb6367780372abef510a7ecd574206b85984b1bcaf`.
The final receipt binds this note; its own hash is supplied separately to
avoid a circular note/receipt hash declaration.
