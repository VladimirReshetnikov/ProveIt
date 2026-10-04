# Exact 2-adic cubic criteria beyond the dyadic branch

The remaining shared-projection83 problem has even non-dyadic q. This note gives an exact criterion for the **2-primary part** of its cubed-scale condition when `t=v2(q)>=2`. It neither makes q dyadic nor proves the native masks. It identifies the cancellation cases that a central-binomial valuation argument must retain, including an explicit cubic exception.

Use the unchanged actual compiler slice and the accepted even-radix theorem. Put `r=(R−1)/2`, so r is odd, and write

```
C_j=binom(2r,r+j),
P(X)=C_0+C_1 X+C_2 X²+C_3 X³,
alpha=v2(X)>=t, h=3t+1.
```

The exact scale condition is `M_r(X)=0 mod 2q³`. Since q divides X, all terms with j>=4 vanish modulo 2q³. In particular its 2-primary condition is exactly `v2(P(X))>=h`. Here X is positive, so P(X)>0 and its valuation is defined. Only this local condition is classified below; every odd-prime condition and the source's exponent, index and transport coupling remain separate.

## 1. Four adjacent valuations

Write `p=popcount(r)`, `k=v2(r+1)`, `ell=v2(r+3)` and `h2=v2(r−1)`. The factorial identity `v2(n!)=n−popcount(n)` gives `v2(C_0)=p`. Consecutive coefficient ratios then give

```
v2(C_0),v2(C_1),v2(C_2),v2(C_3)
       = p, p−k, p+h2−k, p+h2−k−ell.             (1)
```

If k>=2, then h2=ell=1. If k=1, then h2,ell>=2; moreover ell>=3 forces h2=2. The lowest ell bits of r are those of `2^ell−3`, so `ell<=p+1`.

All arguments below use alpha>=2. The case `v2(q)=1,v2(X)=1` is not covered by this note.

## 2. Linear cancellation branch: k>=2

The weighted valuations in P are

```
p, p+alpha−k, p+2alpha+1−k, p+3alpha−k.
```

If k!=alpha, the minimum is unique, giving the exact formula

```
v2(P)=p+min(0,alpha−k).                            (2)
```

If k=alpha, put `X=2^k z` with z odd. Define odd positive integers

```
a0=C_0/2^p, a1=C_1/2^(p−k),
a2=C_2/2^(p+1−k), a3=C_3/2^(p−k).
```

These quotients are integral: p>=k because r ends in k one-bits. Exactly

```
P=2^p G(z),
G(z)=a0+a1 z+2^(k+1)a2 z²+2^(2k)a3 z³.           (3)
```

If p>=h, the local condition holds automatically. Otherwise it is equivalent to `G(z)=0 mod 2^(h−p)`. For every n>=1, G has exactly one odd root class modulo 2^n. Indeed G(1) is even, and its derivative is odd at every integer. For an existing root z modulo 2^n, its two lifts differ in value modulo 2^(n+1) by `2^n G'(z)`; exactly one lifts. This is a complete elementary binary-lifting proof, not an uncharged source operation or an assertion that X can be independently chosen.

Thus a low central valuation is locally repairable only in a precise odd-unit residue class. The complete source additionally fixes `X=2^R−2^u+W`; that coupling is not solved by choosing the root of (3).

## 3. Cubic cancellation branch: k=1

The linear and quadratic terms have valuation strictly above p because alpha>=2. If `ell<3alpha+1`, the cubic term also has valuation above p, so v2(P)=p. If `ell>3alpha+1`, then ell>=3 and h2=2; the cubic term is uniquely least. Together these give, outside equality,

```
v2(P)=p+min(0,1−ell+3alpha),  ell!=3alpha+1.      (4)
```

At `ell=3alpha+1`, h2=2 and p>=ell−1=3alpha. Define odd positive integers

```
b0=C_0/2^p, b1=C_1/2^(p−1),
b2=C_2/2^(p+1), b3=C_3/2^(p−3alpha).
```

Writing `X=2^alpha z`, z odd, gives exactly

```
P=2^p Q(z),
Q(z)=b0+2^(alpha−1)b1 z+2^(2alpha+1)b2 z²+b3 z³. (5)
```

Again p>=h is sufficient; otherwise the exact condition is `Q(z)=0 mod 2^(h−p)`. The derivative is odd at every odd z, and Q has its unique odd residue root modulo2. The same two-lift argument proves a unique odd root class at every higher precision.

Equations (2)–(5) constitute an exact criterion for the local cubic congruence for any odd r>=3 and positive X with alpha>=t>=2. They do not replace the odd-primary conditions in 2q³ or the other source equations.

## 4. The low-central dichotomy and its exceptional family

Suppose `p<h=3t+1` and the local scale condition holds. In Section2 the unique-minimum cases are impossible, so k=alpha. In Section3 the unique-minimum cases are likewise impossible, leaving `ell=3alpha+1`. But then

```
3alpha<=p<=3t, alpha>=t,
```

forcing `alpha=t`, `p=3t` and `ell=3t+1`. The low ell bits already contain ell−1=p ones, so no higher bit can be set. Therefore

```
r=2^(3t+1)−3,  R=2^(3t+2)−5.                     (6)
```

Conversely, for every t>=2, r as in (6), and every positive X with v2(X)=t, the central and cubic terms both have valuation3t, while the two other terms have larger valuations. The normalized two leading units are odd, so their sum is even and `v2(P)>=3t+1`. This is a real local exception. For example `t=2,r=125,X=4` satisfies the 2-primary cubed-scale condition although `popcount(r)=6<7`. This example is not an actual compiler instance or a complete source zero.

Consequently the exact necessary low-central alternatives are

1. `v2(r+1)=v2(X)>=2`, with the linear root-class condition (3); or
2. the explicit family (6), with v2(X)=t.

For an actual compiler zero, the accepted bound `R>3q+1` excludes (6) whenever `2^(3t+2)−5<=3q+1`. Since `q>=B=2^d`, the simple compiler-only condition `3t+1<=d` suffices. In that range every zero either has `popcount(r)>=3t+1` or lies in the linear cancellation branch.

The threshold3t+1 is based on v2(q), not log2(q). When q is non-dyadic it is not the population threshold needed by the old native-mask argument. No native typing, dyadicness or ordinary-input soundness is inferred from it.

## 5. Evidence and remaining coupling

The fresh companion uses exact small binomial coefficients, verifies the nonresonant valuation formulas and both normalized polynomial identities, constructs the unique odd root classes by explicit binary lifting, and checks the low-central dichotomy. It also checks several members of the cubic exceptional family separately. Its receipt pins the three predecessor notes; none of their programs is executed or imported. No entire inherited source, compiler output or large Pell witness is evaluated.

The open work remains the simultaneous constraints at odd primes and the actual fixed compiler's index/exponent/transport relations. A freely liftable local residue does not by itself provide a positive source tuple or a rejected-input counterexample. The 83-operation source remains a candidate; the established universal bound is84 operations.
