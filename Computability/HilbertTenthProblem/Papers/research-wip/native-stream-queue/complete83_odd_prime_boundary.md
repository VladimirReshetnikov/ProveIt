# Odd-prime conditions for the remaining shared83 radix sector

The unchanged shared-projection83 source has an exact, all-size local test at every odd prime divisor of its radix. Outside two explicitly classified valuation ties, the cubed-scale condition is decided by the central binomial valuation and a denominator loss. At a tie, the possible extra cancellation is governed by a simple linear or quadratic congruence. The prime3 case is included.

There is a useful actual-source consequence. Put `Dmask=B−1−MC`. If `p^a || q` is odd and the central binomial coefficient has valuation less than3a, then the **whole prime power p^a** divides one of

```
Z−Dmask*J,    Z−Dmask*J+2.                         (A)
```

This does not assume native binary typing. It narrows the remaining even, non-dyadic sector without excluding it. The exceptional congruences really admit arbitrarily accurate local lifts; central-carry bounds alone cannot replace their audit. No new compiler, source row, witness reduction or universal83 claim is made.

## 1. Inherited domain and exact source binding

Fix a valid inherited compiler slice and a full positive zero of shared83. The accepted offset and even-radix theorems give

```
q=(B−1)J+1 even, X=q*w, Y=s*q^3,
R=3 mod4, r=(R−1)/2 >=24,
X−W=2^R−2^u, X>2^(R−1),
Y=M_r(X)/2,
M_r(X)=sum_(j=0)^r binom(2r,r+j)*X^j.
```

These are inherited mathematical premises, not re-proved by the finite checks below. The recent dyadic exclusion settles the sector q a power of two; this note addresses necessary conditions when q has odd factors.

The actual83 array also binds, literally,

```
C=q−F−Z−alpha−2dx, W=C−Z, u=2dx+b,
R=(q^2−Z−qF)(q^2−1)+(MC+qMF)J,
Ntransport=(K+w)C+q−F−(q−1)*transport_quotient.
```

Here the source MF is the shifted mask, K is Kconstant, and the source name for C is `marked_rhs`. At a positive zero the inherited unit-sign proof gives Ntransport=1. The fresh checker expands the26 actual ancestor rows of these outputs as exact multivariate integer polynomials; it does not run a predecessor helper or substitute arbitrary symbolic cuts without their supplied-input bindings.

## 2. The odd-prime condition uses three terms

Let p be an odd prime dividing q. Write

```
a=v_p(q), b=v_p(X)>=a,
C_j=binom(2r,r+j), c=v_p(C_0),
M_2=C_0+C_1*X+C_2*X^2.
```

For j>=3, X^j is divisible by p^(3a), and2 is invertible modulo that modulus. Consequently

```
p^(3a) | Y  iff  p^(3a) | M_2.                    (1)
```

Thus the cubic term needed at the even modulus2q³ disappears from every odd-prime test. The following identity is over ordinary integers:

```
(r+1)(r+2)*M_2 = C_0*N,
N=(r+1)(r+2)+r(r+2)*X+r(r−1)*X^2.                 (2)
```

It follows immediately from the two successive binomial-coefficient ratios. In particular

```
v_p(M_2)=c+v_p(N)−v_p((r+1)(r+2)).                (3)
```

Every quantity is positive, so no valuation of zero is used. Equations(1)–(3) are an exact finite arithmetic test for each odd prime power, not merely a lower bound.

## 3. Complete valuation split, including p=3

If p divides neither r+1 nor r+2, equation(2) has unit constant term and its remaining terms are divisible by p. Hence

```
v_p(M_2)=c.                                       (4)
```

The consecutive denominators cannot both be divisible by the odd p.

**Linear branch.** Suppose d=v_p(r+1)>0. The three summands in M_2 have valuations

```
c, c+b−d, c+2b−d.
```

Here r,r−1,r+2 are all p-units. If d≠b the lowest valuation is unique, so exactly

```
v_p(M_2)=c+min(0,b−d).                            (5)
```

At the sole tie d=b, put eta=(r+1)/p^b and z=X/p^b. Both are units. Equation(2) gives

```
N=p^b*F_1(z),
F_1(z)=eta(r+2)+r(r+2)z+r(r−1)p^b z^2,
v_p(M_2)=c+v_p(F_1(z)),
F_1(z)=eta−z modp.                                (6)
```

Thus a first extra factor of p occurs exactly when eta=z modp.

**Quadratic branch.** Suppose d=v_p(r+2)>0 and let e=v_p(r−1). The three summand valuations are now

```
c, c+b, c+2b+e−d.
```

If d≠2b+e, the minimum is unique and

```
v_p(M_2)=c+min(0,2b+e−d).                         (7)
```

At a tie, eta=(r+2)/p^d and zeta=(r−1)/p^e are units, and

```
N=p^d*F_2(z),
F_2(z)=(r+1)eta+r*eta*p^b*z+r*zeta*z^2,
v_p(M_2)=c+v_p(F_2(z)).                           (8)
```

For p>=5, e=0 and d=2b. Reduction gives F_2(z)=−eta+6z² modp. For p=3, the tie has d>e, while (r+2)−(r−1)=3; hence e=1 and d=2b+1. Then zeta=−1 mod3 and F_2(z)=−eta+2z² mod3. Thus the p=3 branch is not obtained by incorrectly dividing by6 modulo3.

Uniformly, a quadratic tie means

```
d=2b+v_p(6),
F_2(z)=0 modp  iff
r+2=6X^2 mod p^(2b+v_p(6)+1).                    (9)
```

The valuation split is exhaustive. No restriction on the size of r, p, q or the positive source witnesses is added.

## 4. A necessary source-word congruence when central carries are insufficient

If c<3a, neither a regular prime nor a non-tied denominator branch can pass(1): formulas(4),(5),(7) give a valuation at most c. Therefore either

```
v_p(r+1)=b,
r+1=X mod p^(b+1),                               (10)
```

or

```
v_p(r+2)=2b+v_p(6),
r+2=6X^2 mod p^(2b+v_p(6)+1).                    (11)
```

The displayed congruences are only the first required cancellation. For the exact higher threshold, equations(6),(8) require the actual supplied z=X/p^b to satisfy F_h(z)=0 mod p^(3a−c).

Since b>=a, (10) implies p^a divides R+1, whereas (11) implies p^a divides R+3. The literal source gives the stronger exact polynomial identity

```
R−(Z−Dmask*J−1)
=q*(q^3−q−Z*q−q^2*F+F+MF*J+1).                  (12)
```

This identity uses (B−1)J=q−1 and is independently expanded from the actual rows. Combining(10)–(12) proves(A).

Let q_def be the product of the full prime powers p^a || q over odd p with c<3a. Then

```
q_def | (Z−Dmask*J)(Z−Dmask*J+2).                 (13)
```

Each such odd prime belongs to exactly one factor, since their difference is2. The factors need not be positive; zero is allowed. Formula(13) requires no native digit interpretation of Z or J. Root suggested this source-level pullback; the full-prime-power strengthening follows from b>=a.

For clarity, c itself is exactly computable from the finite factorial-valuation formula

```
c=sum_(j>=1) [floor(2r/p^j)−2floor(r/p^j)].       (14)
```

Its summands are0 or1. In the linear denominator branch the low d base-p digits give at least d carries. In the quadratic branch they give at least d carries for p>=5, and at least d−1 for p=3. These facts agree with integrality of the binomial coefficients but do not force the required3a bound in every case.

## 5. Why a tied branch cannot simply be discarded

At a root of F_1 modp, its derivative is−1 modp. At a unit root of F_2 modp, its derivative is2kz with k=6 modp for p>=5 and k=2 mod3 for p=3, hence nonzero. Therefore each residue root extends uniquely through every precision.

Here is the elementary lifting argument, so no external p-adic theorem is needed. If F(z)=0 modp^n and p does not divide F'(z), then

```
F(z+t*p^n)=F(z)+t*p^n*F'(z) modp^(n+1).
```

Exactly one t in{0,...,p−1} makes the right side vanish. Induction gives a unit z modulo p^N for every N. The linear branch always has one unit starting root. The quadratic branch has two starting roots exactly when eta/k is a nonzero square modulo p. For p=3 this is precisely eta=2 mod3; otherwise it has no unit root.

Thus the normalized three-term polynomial admits arbitrarily high cancellation in the permitted local residue classes. For example, the fresh evidence uses r=29,p=5,b=1, where c=1 and the linear tie has one root, and r=145,p=7,b=1, where c=2 and the quadratic tie has two roots. These test a specific previously unjustified shortcut—replacing the cubed-scale condition by c>=3a. They are local prime-power examples only, not additional scalar full-zero constructions.

In a real candidate tuple, X is already constrained by

```
X=2^R−2^u+W,
```

and R,u,W come from the same source. The lifting argument does not choose those values independently, does not solve their simultaneous equations, and does not prove a valid-compiler non-dyadic zero.

## 6. Transport and two suggested radix families

The transport unit gives, with m=q−1,

```
(K+w)C=F modm.                                    (15)
```

The right side is F, not F−1: reducing +q−F and the unit+1 cancels those two ones. Therefore a residue w exists exactly when

```
gcd(C,m) divides F.                               (16)
```

When compatible, it is one residue class modulo m/gcd(C,m), or gcd(C,m) classes modulo m. The positive quotient can be obtained by taking a sufficiently large positive representative when C>0. In the valid pretyping range C=0 is impossible: (16) would require m|F, while0<F<q−1. These are local transport facts only; w remains bound to X/q in the full source.

Since gcd(q,q−1)=1, transport adds no same-prime denominator at any p|q. This separates congruence bookkeeping; it is not permission to vary X freely after fixing the source.

Tesla's separate constructive work suggested the following exact outer radix families, with B=2^d:

| q | J | odd-prime period m_p | v_p(X) when W=0 and m_p divides R−u |
|---|---|---|---|
| B(B+1)/2 | B/2+1 | 2d for p dividing B+1 | a+v_p((R−u)/(2d)) |
| B(2B−1) | 2B+1 | d+1 for p dividing2B−1 | a+v_p((R−u)/(d+1)) |

Here a=v_p(q). Both rows satisfy q=(B−1)J+1. For the first family v_p(2^(2d)−1)=v_p(B+1)=a, since the odd p cannot divide B−1 as well. The second has v_p(2^(d+1)−1)=a directly. The valuation formulas follow from

```
v_p(A^n−1)=v_p(A−1)+v_p(n),  p odd, A=1 modp.
```

To verify this identity, write A=1+v with p|v. Raising to an exponent prime to p leaves the linear binomial term uniquely minimal; raising to p increases its valuation by exactly1, all remaining terms being strictly larger. Factor n into its p-power and coprime parts.

The source residue for R also simplifies: it is Z+MC/2 modp in the first family and Z+2MC modp in the second. Here the fraction denotes the inverse of2 modulo p. These formulas can be used with Sections3–4 without constructing the enormous X. No assertion is made here that a family's cubed-scale constraints pass, that its slacks are positive, or that it supplies all native witnesses; that is a separate constructive problem.

## 7. Fresh evidence and exact limits

The companion helper is newly written standard-library code. It authenticates four frozen files as inert bytes and checks:

* eight actual source-bound output identities through their26-row ancestor union, plus the exact packed-index identity(12);
* 56,700 odd-prime valuation cases, including2,120 ties and362 first cancellations;
* nine local residue roots across six examples, uniquely lifted to precision p^7;
* 969 complete small half-binomial sums against the four-term even-radix truncation, and816 odd-prime three-term reductions;
* 20,520 transport compatibility cases, including the zero-C boundary;
* 160 checks of the two radix-family valuation formulas for d=2,...,12 using exact modular exponentiation.

These finite checks corroborate the proofs above. They neither prove the all-size results by enumeration nor synthesize a compiler output, a Pell tuple, or a full source zero. The source is read as data; no supplied, archived, committed, frozen or predecessor program is executed or imported. There is no new complete-DAG or degree audit: unchanged83=46M+37A,18 witnesses and degree187 remain inherited from the separately reviewed source packet.

Full prose read for this note consists of the shared-projection offset theorem, even-radix boundary and dyadic zero-offset exclusion, plus the source receipt. Earlier Pell classification, the valid compiler construction and all accepted pretyping proofs retain their prior review scopes. The source-word corollary and local congruence classification are new; neither resolves the remaining even non-dyadic sector.

The companion JSON records all exact dependency and helper hashes. Fresh normal and optimized-Python receipt replays passed from / before freezing this packet; no predecessor was replayed.
