# Carry budgets and a source obstruction in the odd-primary family

The remaining odd-primary problem cannot be settled merely by forcing one denominator resonance. An exact carry decomposition identifies what a linear resonance still needs. A quadratic resonance supplies a larger carry budget automatically, but the actual fixed source and positive raw slack prevent forcing quadratic resonance at **every** odd prime simultaneously by the existing shortcut F=Kz.

More precisely, in either frozen non-dyadic family, for every n>=5 and every positive z retaining C=Z=z, F=Kz and the positive original slack, neither R+1 nor R+3 is divisible by A², where A is the entire odd factor of q. For the original odd-R family members this is equivalently the same exclusion for r+1 and r+2. This rules out a particular all-prime divisibility strategy. It does not rule out the family, prove or disprove its odd-primary scale condition, or give a universal83 theorem.

The input-variation idea motivating the carry budget is being developed separately by Tesla. No result of that new construction is needed to prove this note. The unchanged source remains83 operations and18 witnesses; no polynomial or coordinate is altered.

## 1. Exact extra carries at the two resonances

For an odd prime p define

```
c_p(v)=v_p(binomial(2v,v)).
```

The finite factorial formula gives

```
c_p(v)=sum_(j>=1)[floor(2v/p^j)−2floor(v/p^j)].   (1)
```

Every summand is0 or1; it is the carry into the corresponding base-p position when v is doubled.

### Linear resonance

Suppose r+1=p^b h, where b>=1 and p does not divide h. Then exactly

```
c_p(r)=b+c_p(h).                                 (2)
```

For j<=b the low digits of r are all p−1, so each contributes1 to(1). For j=b+k, k>=1, the two floors are

```
floor((2h−1)/p^k), floor((h−1)/p^k).
```

Since neither h nor2h is divisible by p, these equal floor(2h/p^k) and floor(h/p^k). The remaining sum is precisely c_p(h).

At a source prime p^a || q, a linear tie has b=v_p(X). If the input-variation construction forces b=a+tau, then

```
c_p(r)>=2a  iff  c_p(h)>=a−tau.                  (3)
```

The right side is automatic only when tau>=a; otherwise it is a real additional carry requirement in the quotient h. Equations(2),(3) do not infer it from the magnitude of r.

There is an unbounded counterexample to that inference alone. For every odd prime p, a>=1 and L>=1, put

```
h=p^L+1, r=p^a h−1.
```

Doubling h produces no base-p carries, so c_p(h)=0. Thus r can be arbitrarily large, r is odd, R=2r+1 is3 modulo4, and

```
v_p(r+1)=a,  c_p(r)=a<2a.                        (4)
```

This is a counterexample only to the proposed implication from resonance, parity and size to the extra carry budget. It is not a choice of the actual compiler constants, an outer-family member, a Pell tuple or a source zero.

### Quadratic resonance

For p>=5, if r+2=p^d h with p not dividing h, then the same floor argument gives

```
c_p(r)=d+c_p(h).                                 (5)
```

The low d digits of p^d h−2 all produce carries: its units digit is p−2, whose double is at least p, and each subsequent low digit is p−1. For the higher floors, p^d>=5 ensures the small subtraction does not cross another integer; p not dividing h again identifies the remaining sum with c_p(h).

In the p=3 quadratic resonance, d>=3. The units digit of3^d h−2 is1 and gives no carry; the other d−1 low digits do give carries. Hence

```
c_3(r)=d−1+c_3(h).                               (6)
```

The exact odd-prime boundary theorem says a quadratic tie has

```
d=v_p(r+2)=2b+v_p(6), b=v_p(X).
```

Combining(5),(6) yields the uniform identity

```
c_p(r)=2b+c_p(h)>=2b>=2a                         (7)
```

for every odd p, including3. Thus the quadratic branch does not need the extra hypothesis in(3). It still requires its square-unit congruence and any higher root precision from the odd-prime boundary theorem.

## 2. Actual source constants and the whole odd factor

Retain the frozen actual-compiler family with B=2^d, d an odd power of five, d>=25, n=1 modulo4 and Q=B^n. Put m=B−1. The two shapes are conveniently written

```
A=Q+1,   epsilon=−1    (plus family),
A=2Q−1,  epsilon=+1    (minus family),
q=A(A+epsilon)/2,
J=(q−1)/m.                                      (8)
```

A is exactly the odd part of q. In particular gcd(A,2m)=1: if an odd prime divided both A and m, it would divide both q and mJ=q−1. There are no odd denominator primes from m to discard in the following argument.

The actual fixed coefficients have the properties

```
0<MC<m, MC even;
0<MF<2m, MF odd;
K even, K+2>4m.                                 (9)
```

Here MF is the shifted source port MF_source, not the unshifted native mask. The source bindings for(9) matter:

* The modified75 native mask is MF_old+4, with its old low three bits zero. Adding B−1 makes MF_source odd.
* Every exponent in DC is positive, including the optional high monomial. Thus the inner radix V=2^b divides DC. Also DR=V^H with H>=1 and V>=32. Hence K=DC+B*DR is even and exceeds32B, which is stronger than K+2>4m.
* The complete76/modified75 mask statements supply MC even and the displayed ranges.

These statements are read from the actual compiler proofs and literal sparse coefficient definitions; no compiler was executed to obtain a substitute scalar table.

For the obstruction stated in terms of R, we allow any positive integer z, not merely the original bounded choice z<=4d. The translation to an integer r=(R−1)/2 is restricted to odd R, including the original family z=1 modulo4. Preserve

```
C=Z=z, F=Kz,
alpha=q−(K+2)z−2dx>0, x>0.                      (10)
```

The unchanged packed source is

```
R=q^4−Kz*q^3−(z+1)q²+Kz*q+z+(MC+qMF)J.          (11)
```

The constant +z is retained. In particular(10) gives

```
z<q/(K+2).                                      (12)
```

## 3. Exact congruence modulo A²

For c in{1,3}, define the fixed-coefficient linear polynomial in A

```
P_(epsilon,c)(A)
 =2(MC−c*m)
  −epsilon*A*[MC−MF+K(MC−c*m)].                  (13)
```

Then on the source family,

```
A² divides R+c
iff A² divides 2m*z−P_(epsilon,c)(A).            (14)
```

To derive it without losing a constant, multiply(11) by m and use mJ=q−1:

```
mR=mq^4−mKz*q^3+[MF−m(z+1)]q²
   +(mKz+MC−MF)q+mz−MC.
```

Modulo A², q=epsilon*A/2 and q²=0. Hence

```
m(R+c)=m(z+c)−MC
       +(epsilon*A/2)(mKz+MC−MF) mod A².
```

Multiplication by2−epsilon*A*K cancels the first-order z correction and gives

```
(2−epsilon*A*K)*m(R+c)
 =2m*z−P_(epsilon,c)(A) mod A².                  (15)
```

All relevant denominators and factors are units modulo the odd A²:2,m and2−epsilon*A*K are coprime to A. The fresh formal check clears the powers of2 and verifies an exact integer-polynomial remainder divisible by A², including the source +z term.

## 4. Positivity obstructs simultaneous deep divisibility

Assume

```
A>2m(3K+8).                                     (16)
```

For c=1 or3, the fixed ranges in(9) imply

```
|MC−c*m|<c*m,
|MC−MF|<2m,
|P_(epsilon,c)(A)|
 <m[2c+(cK+2)A]
 <=m(3K+8)A<A²/2.                               (17)
```

Since MC is even, MF is odd and K is even, the bracket in(13) is odd. A is odd, so P_(epsilon,c)(A) is odd.

If A² divided R+c, equation(14) would give an integer j satisfying

```
2m*z=P_(epsilon,c)(A)+j*A².                      (18)
```

Its parity forces j odd. The positivity z>0 and the bound |P|<A²/2 then force j>=1; a nonpositive odd j makes the right side negative. Thus

```
z>A²/(4m).                                      (19)
```

But q=A(A+epsilon)/2<A², and(9),(12) give

```
z<q/(K+2)<A²/(4m),                              (20)
```

a contradiction. We have proved, under(16),

```
A² does not divide R+1,
A² does not divide R+3.                          (21)
```

For the original odd-R members, r=(R−1)/2 is an integer. Because A is odd, (21) is then equivalent to A² not dividing r+1 and r+2 respectively.

The bound(16) holds for every actual-family n>=5. The frozen fixed-constant margin K+2<4B^(5/4) yields

```
2m(3K+8)<28B^(9/4)<B³,
```

where the final inequality uses B=2^d with d>=25. On the other hand both shapes have A>=B^5 when n>=5. Therefore(21) applies throughout that tail, including any alternative positive z satisfying(10).

## 5. What this rules out, and what it leaves

Suppose one tried to force the quadratic resonance at every odd p^a || A. Its required depth is2b+v_p(6), with b=v_p(X)>=a, so every p^(2a) would divide r+2. Their product A² would divide r+2, contradicting(21). The same obstruction rules out forcing v_p(r+1)>=2a simultaneously at every odd divisor merely to guarantee2a central carries.

This is a restriction on those **simultaneous source-divisibility strategies**, not on all possible carry mechanisms. In particular:

* A linear tie at depth b=a+tau can still acquire its missing a−tau carries in the quotient h, as equation(2) states.
* Primes with c_p(r)>=3a need no cancellation tie at all.
* Different odd primes may use different branches. The argument does not exclude a proper subset of quadratic ties.
* Changing F independently of Kz falls outside(10); its transport and positivity would need a new proof.

The all-size counterfamily(4) shows why resonance and a large packed index alone do not prove the remaining quotient carry bound. It does not decide that bound for the actual source polynomial. Conversely, the useful carry budget in(7) cannot be converted into an all-prime construction by simply choosing one enormous z residue: the positive raw slack prevents it for the current F=Kz family.

No completed member, rejected-input example, odd-primary divisibility theorem for the full family, or universal83 claim follows from this note.

## 6. Exact evidence and read scope

The fresh standard-library helper authenticates the unchanged source and eight relevant proof/source files as inert bytes. It guards13 literal outer source rows and formally verifies(15) for both signs after clearing denominators. Fresh arithmetic checks include:

* 1,250 small exact-binomial checks of the factorial valuation formula;
* 2,085 instances each of the linear and quadratic quotient-carry identities;
* 120 members of the unbounded counterfamily(4), checked by finite factorial valuations;
* 32 exact affine source-congruence roots at A², all violating the required positive raw slack as predicted.

The last checks use synthetic relaxed coefficient data satisfying the theorem's scalar hypotheses. They are not materialized compiler outputs or native zeros. No huge half-binomial integer, X=2^R, or Pell witness is evaluated. Finite checks corroborate the proofs; they do not replace their quantifiers.

Read scope consists of the full frozen outer-family and odd-prime notes; the unchanged source receipt; modified75 compiler proof Section1 and its mask-export definitions; complete76 proof Section1 and its sparse coefficient construction; and complete78's displayed DC/DR formulas and corresponding accessors. The sparse compiler files are read as text only. No previous helper, archive, supplied program or builder is executed or imported. Full predecessor mathematical and circuit audits remain inherited at their original scope.

**Correction remark1 (retained pre-freeze scope error).** The initial draft stated the r+1/r+2 equivalence after allowing every positive z without explicitly requiring odd R. The source has R=z modulo2, so an even z gives even R and (R−1)/2 is not an integer. The general obstruction is now stated for R+1 and R+3; its r formulation is explicitly restricted to the original odd-R family members. No equation or bound in the R obstruction changes.

The companion JSON records dependency pins, the fresh helper hash and detailed evidence. Fresh normal and optimized-Python exact checks passed from / before freeze. No repository or Git operation is performed by this packet.
