# Independent mathematical review of the fifteen-integer parity norm

## Scope and conclusion

The algebraic reduction from the authenticated seventeen-integer source to
the proposed fifteen-integer equation is sound. The review checked the
guard-only prerequisites, denominator clearing, every exceptional sign
case, the three-radical argument, rational Pell descent, reconstruction of
all three removed integers, and the positive unit-product finalizer.
No missing branch or denominator gap was found.

This review concerns the ordinary, unbounded mathematical proof. It does
not independently certify the generated circuit's operation count, exact
degree, coefficient bytes, or the inherited native/compiler-to-refutation
calibration. Those require the separate artifact and provenance audits. It
is an independent AI-assisted review, not an external human peer review or
a new Lean/Rocq certificate.

## 1. Notation and claimed projection

Use the source seventeen-variable abbreviations, and put

```
d = c^4,
Q = Delta*(f^2-1),
delta = Q-1,
m = X*Y^2,
B0 = m*k,
S = k*(2*m+1),
A0 = 1+m*(m+1)*k^2,
L = 2*n0+1+2*B0+2*S*V.
```

The independent new coordinate is `n0`. All coordinates are unrestricted
integers. The three deleted source coordinates are `r,tau,nu`.

The rational radicands are

```
A = 4*A0,
B = Q/d,
C = 4*S^2*(Q*V^2-1)/(Q-1).
```

The intended relation is that `L` is a signed sum of their three square
roots. Importantly, `L` is always an odd, nonzero integer. This parity is
what excludes the extraneous rational sums obtainable by cancellation of
two irrational radicals.

## 2. Prerequisites follow before extracting any missing root

The joint guard gives `det>0` and `eta*zeta>0`. Its positive right side is
`1+p1^2+p2^2+p3*(p3+1)`. If both guard arguments were negative, the squared
term would exceed their product, so the positive product cannot come from
two negative arguments.

The determinant implication gives `q!=0`. The fixed tuple has `beta>=17`,
and `q=beta*(3*J+1)+1`, so `|q|>=16` independently of any Pell row.
Similarly `|W|>=4`, `|X|>=64`, and `|Y|>=4096` from their affine residue
definitions. Therefore `|m|>1` and

```
|a| = |(X+1)*Y| >= (|X|-1)*|Y| > 4,
Delta = (a+2)^2-1 > 1.
```

Since `eta,zeta` are nonzero integers of the same sign and
`k=eta+zeta`, we have `|k|>=2` and `0<|eta|<|k|`. Consequently

```
|c| = |Y*k+eta| > |k|*(|Y|-1) > 0.
```

Thus `d>0`. Also `m*(m+1)>0`, `A0>0`, `S!=0`, and the exact identity

```
S^2-4*A0 = k^2-4 >= 0
```

holds. None of these arguments uses the deleted first Pell norm, deleted
strong square condition, deleted auxiliary Pell norm, or a bootstrap
theorem that assumes any of those conditions.

Finally `Q=1` is impossible: the positive integer `Delta>1` divides `Q`.
Therefore the common denominator `D=d*(Q-1)` is nonzero before the norm is
divided by any expression.

## 3. The polynomial is exactly a cleared eight-factor norm

For arbitrary rational `A,B,C`, define

```
F(L) = ((L^2-A-B-C)^2-4*(A*B+A*C+B*C))^2
       -64*A*B*C*L^2.
```

Over the complex numbers this equals the product of

```
L-e1*sqrt(A)-e2*sqrt(B)-e3*sqrt(C)
```

over all eight independent choices `e1,e2,e3` in `{1,-1}`. The identity
is polynomial and remains valid if a radicand is zero or square classes
coincide. It follows by repeated difference-of-squares factorization.

The proposed scaled quantities satisfy

```
Abar = 4*A0*D       = A*D,
Bbar = Q*(Q-1)     = B*D,
Cbar = 4*S^2*d*(Q*V^2-1) = C*D.
```

Thus the supplied numerator

```
R = D*L^2-Abar-Bbar-Cbar,
N = (R^2-4*(Abar*Bbar+Abar*Cbar+Bbar*Cbar))^2
    -64*Abar*Bbar*Cbar*D*L^2
```

is exactly `D^4*F(L)`. Since `D!=0`, its zeros are exactly the zeros of
the rational norm. In particular, a negative `D` in the cases `Q<=0`
causes no change: the scaling factor is its fourth power.

## 4. Exceptional values cannot give a zero

If `Q<0`, then `A>0`, `B<0`, and `C>0`. A signed sum of their square
roots has exactly one nonzero imaginary contribution, so it cannot equal
the real integer `L`.

If `Q=0`, then `B=0` and `C=4*S^2`. A norm zero would imply
`L=+/-2*sqrt(A0)+/-2*|S|`. Therefore `sqrt(A0)` would be rational and
hence integral, because `A0` is an integer. The right side would be even,
contradicting odd `L`.

If `Q>1` and `V=0`, then `A,B>0` but `C<0`. Again exactly one nonzero
imaginary contribution prevents a real root.

The remaining case is `Q>1` and `|V|>=1`. All three radicands are now
strictly positive, and

```
C >= 4*S^2 >= 16*A0 > 4*A0 = A.
```

In particular their first and third square roots cannot cancel each
other. This strict inequality is obtained without assuming either root
is rational or integral.

## 5. Rational Pell descent has the required denominator strength

For integers `Q>1,V`, suppose a rational `y` satisfies

```
Q*V^2-(Q-1)*y^2 = 1.
```

Then `y` is an integer. Here is a full denominator-preserving descent.
Write `y=a/e` in lowest terms, with `e>0`. Clearing denominators and using
`gcd(a,e)=1` gives `e^2 | (Q-1)`. Both `V` and `y` are nonzero; take
absolute values. If `V=1`, the equation gives `y=1`, hence `e=1`.

For `V>1`, put

```
V' = (2*Q-1)*V-2*(Q-1)*y,
y' = (2*Q-1)*y-2*Q*V.
```

The first coordinate is an integer because `e | (Q-1)`. The denominator
of `y'` after reduction is exactly `e`: its numerator modulo `e` is
`(2*Q-1)*a`, and `2*Q-1=1 mod e`. The determinant-one transformation
preserves the displayed norm.

The original norm gives `y>V` and `Q*V>(Q-1)*y`. The first inequality
implies `V'<V`; the second gives `V'>-V`. The preserved norm excludes
`V'=0`. Thus `0<|V'|<V`. Replacing both transformed coordinates by their
absolute values preserves the norm and denominator. Strong induction on
the positive integer `V` reaches `V=1` while preserving `e`, proving
`e=1`. No assumption that `Q` is a square is needed.

This verifies the exact source69 descent used here; in particular, merely
knowing that a transformed denominator divides the old denominator would
not suffice, but the stronger equality is available.

## 6. Oddness excludes every irrational cancellation

A nonzero rational signed sum of three positive rational square roots has
only two possibilities: all three roots are rational, or two irrational
roots cancel and the remaining root is rational. To see this, group terms
by their classes in `Q*/Q*^2`. Distinct classes give linearly independent
radicals over the rationals. With only three terms, every nontrivial class
must either have two terms cancelling or all three terms must occupy the
same class. The latter can only produce rational zero, excluded by the
nonzero value of `L`.

Cancellation of the first and third roots is impossible by `C>A`.
If the first and second roots cancel, the remaining third root is rational.
Divide that signed root by `2*S`. The quotient is rational and obeys the
Pell equation in Section 5, so it is integral. The remaining root is
therefore even. If the second and third roots cancel, the remaining first
root is `+/-2*sqrt(A0)`; rationality makes `sqrt(A0)` integral, so this
root is also even. Both cases contradict odd `L`.

Therefore every norm zero in the remaining positive case has three
rational signed roots.

## 7. All three removed source coordinates are integral

Choose the signed roots giving

```
L = 2*tau_old + u + 2*S*y.
```

The first root gives `tau_old^2=A0`; rational square integrality makes
`tau_old` an integer. The third root gives
`Q*V^2-(Q-1)*y^2=1`; Section 5 makes `y` an integer. This definition is
valid for either sign of `S`; taking the signed third root divided by
`2*S` handles negative `S` explicitly.

The second root satisfies `u^2=Q/d`. The displayed sum makes `u` an odd
integer, since `L` is odd and both other summands are even integers. Define

```
r = (u-1)/2,
I = u*c^2,
tau = tau_old-B0,
nu = y-V.
```

All restored coordinates are integers. They satisfy `I=(2*r+1)*c^2` and
`I^2=Q`, so the strong source condition holds. The two deleted centered
norms hold because they are exactly

```
(tau+B0)^2-A0 = 0,
Q*V^2-(Q-1)*(nu+V)^2-1 = 0.
```

The original `main` and `guard` conditions are retained. Comparing the
expressions for `L` also recovers `n0=r+tau+S*nu`; no additional constraint
on the retained coordinate has been introduced.

Conversely, at any source seventeen-variable zero, take
`n0=r+tau+S*nu`. The three signed roots are respectively
`2*(tau+B0)`, `2*r+1`, and `2*S*(nu+V)`, so one of the eight norm factors
vanishes. This is the full two-way existential projection, without a
restriction to canonical positive witnesses.

## 8. One-equation finalizer

Let `G=main^2+guard^2`. For integer assignments `G>=0`. The proposed single
equation `G+N+G*N=0` is equivalent to

```
(1+G)*(1+N)=1.
```

The first factor is a positive integer. Therefore both factors equal one,
forcing `G=N=0`. The converse is immediate. No unproved nonnegativity
condition on the cleared norm `N` is used.

Together, these arguments establish the claimed equivalence to the source
seventeen-variable zero set after existentially restoring the three deleted
coordinates and projecting the new one. The source's logical calibration
can then be composed exactly as before.
