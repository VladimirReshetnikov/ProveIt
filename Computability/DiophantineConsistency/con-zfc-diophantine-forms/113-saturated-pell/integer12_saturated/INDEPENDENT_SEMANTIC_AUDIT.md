# Independent semantic audit: saturated scalar twelve-integer equation

## Verdict and scope

The new saturation is sound and complete over twelve **unrestricted
integer** coordinates, under the same explicitly inherited ordinary
native/refutation calibration as the accepted scalar-carrier parent.
I found no additional arithmetic hypothesis or exceptional-case gap.
This is independent mathematical review within the present AI
collaboration, not external human review or a proof-assistant result.
Operation counts, exact total degree, and coefficient payload hashes
remain separate artifact checks.

Inspected sources (paths relative to this twelve-integer packet):

* `build.py`, including the literal
  definitions before the equivalent direct evaluation of 81Dg;
* `parent/PROOF.md`, Sections 2--5;
* `parent/source/PRIME_TWELVE.md`, Sections 2--5;
* `parent/source/signed-quadratic-proof.md`, Sections 2, 4, and 5;
* `parent/source/INTERPOLATION12.md`, Sections 5--7;
* `parent/source/RESIDUE_AND_DETERMINANT.md`, Sections 3--5.

The exact new scalar definitions being reviewed are

```
U=s*r*c^2,
Dt=1+XY^2(XY^2+1)k^2,
Df=1+Delta*U^2*Dt,
Q=Delta^2*U^2*Dt,
delta=Q-1,
b=c-R+4U*Dt*T,
V=Df*b-c,
Cy=Q*V^2-1,
G2=Dt*Df,
S=U*H^5,
Ac=Phi_H(H*T+K), K=X(X+2ac)-1,
Phi_H(z)=(z^2+3H^2)(z^3-19H^3).
```

The rational chart has `Z=S(n+V)-Ac` and normalized roots
`3sqrt(G2), 9sqrt(Dg), sqrt(Cy/delta)`. The integral chart has
`Z=S(n+delta V)-Ac`, with last root `sqrt(delta Cy)` instead.
The proof also applies if 81Dg is evaluated directly as
`(243Pair-324)s^2+81`.

## 1. Arbitrary signed inputs and all zero cases

The inherited affine restrictions hold identically for all integers.
They give nonzero even q, q=2 modulo 3, nonzero W0=12w+4,
X=qW0, and Y=(2v+1)q^3. The lower bounds are |q|>=16,
|X|>=64, and |Y|>=4096. Thus a=(X+1)Y has large nonzero
absolute value, Delta=(a+2)^2-1>1, and H=4a+3 is nonzero and odd.

For every integer ell, ell(ell+1)>=0, so Dt>=1 even when X<0.
Consequently Df>=1. Q is zero if U=0 and otherwise
Q>=Delta^2>1; in particular delta never vanishes.

If U=0, then S=0, Df=1, Q=0, delta=-1, and every scaled
radicand vanishes. Both finalizers specialize exactly to Ac^8.
But Ac=H^5*pi(T+K/H), where pi(x)=(x^2+3)(x^3-19) has no
rational zero. Therefore no polynomial zero has U=0. This covers
s=0, r=0, and c=0 simultaneously.

At a zero U is nonzero, so s,r,c are nonzero and |U|>=c^2.
Then Df>|c|+1. Since b is integral, b=0 gives V=-c, while
b!=0 gives |V|>=Df-|c|>1. Thus V cannot vanish and Cy>0.
The auxiliary radicands Cy/delta and delta*Cy are positive.

Dg is the only potentially negative radicand. With S nonzero, a
negative Dg would contribute the only nonzero imaginary term to a
vanishing conjugate factor. Therefore Dg>=0. Since s is a nonzero
integer, Pair<=0 would imply Dg=(3Pair-4)s^2+1<=-3. Hence
Pair>0; the joint positivity lemma gives G>0 and eta*zeta>0.
No sign of q,X,Y,c,U,V,H was used in this bootstrap.

Dg=0 is harmless: omit the zero radical in the separation argument.
Dt=1 is also algebraically harmless for coprime splitting. After the
strict guards k cannot vanish, so in fact Dt>1, but this is unnecessary.

## 2. Mod-3 root separation and coprime splitting

Modulo 3, the affine restrictions give X=-1 and a=H=Delta=0.
Moreover ell=XY^2 is either 0 or -1 modulo 3, so Dt=1 modulo 3
without any restriction on Y. Consequently

```
Df=G2=1, Q=0, delta=Cy=-1 mod 3.
```

After division by nonzero S, the squared 3-adic orders of the
nonzero normalized roots are 0 for the auxiliary root, 2 for
3sqrt(G2), and 4+v3(Dg)>=4 for 9sqrt(Dg). The same auxiliary
order is zero in the integral chart. Every subset with at least two
roots has a unique even minimum squared valuation. The full
prime-order separation lemma in PRIME_TWELVE Section 3 makes every
root rational, without assuming independence of square classes.

Thus G2 and Dg are integer squares. Since

```
gcd(Dt,Df)=gcd(Dt,1+Delta*U^2*Dt)=1,
```

write Dt=tau^2 and Df=f^2 with positive integer tau,f. The product
root is f*tau. The remaining rational y satisfies
QV^2-(Q-1)y^2=1; in the integral chart first set
y=sqrt(delta Cy)/delta. Here Q>1 and V is a nonzero integer.
The adjacent-Pell descent makes y integral for either sign of V:
if m is its reduced denominator, m^2 divides Q-1, and the transform

```
V'=(2Q-1)|V|-2(Q-1)|y|,
y'=(2Q-1)|y|-2Q|V|
```

strictly decreases the absolute integer first coordinate while
preserving m. Descent to |V|=1 forces m=1.

## 3. Scalar projection and exact restoration of the signed kernel

The normalized root sum is integral, so S divides Ac in both charts.
Therefore H^5 divides Phi_H(HT+K). For p^e exactly dividing H,
if b=v_p(HT+K)<e, the leading term in

```
Phi_H(z)=z^5+3H^2 z^3-19H^3 z^2-57H^5
```

has order 5b, strictly below the other terms. This contradicts
divisibility by p^(5e). Hence H|K, also for negative H. No
coprimality of H and U is needed.

Define proof-only old coordinates

```
I=U*tau, r_old=r*tau, T_old=tau*T.
```

They are integers, I is nonzero, and exactly

```
I=s*r_old*c^2,
Df=1+Delta I^2, Q=(Delta I)^2,
V=Df*(c-R+4I*T_old)-c.
```

In particular c^2 divides I. The essential identity is
I*T_old=U*tau^2*T=U*Dt*T; using T itself as the old auxiliary
coordinate would be incorrect.

The signed main-root elimination is invoked only at its stated
interface: a nonzero integer I divisible by c^2, the exact strong and
auxiliary norms and two auxiliary congruences, the unchanged first
norm, both strict guards, the cubic scale Y, and H|K. It first gives
absolute main classification, then pre-projection rank and ratio
bootstrap, then the whole-product projection. It recovers
sigma*X=2^R, sigma=sign(c), and a signed main root d with
H|(d-X-ac). Only then does X=2 modulo 3 choose the positive
orientation.

The arbitrary nonzero strong multiplier is explicitly licensed by
INTERPOLATION12 Section 5. Its Lucas multiplication argument uses
c^2|I to prove both p|m and |c||m, with no oddness assumption on
r_old. One must not introduce the potentially nonintegral expression
(Delta*s*r_old-1)/2.

This restores the generalized signed native kernel, whose ordinary
native/refutation theorem is inherited. It is not a pointwise map to
the old scalar-carrier polynomial: that carrier would use T_old and
I*H^5. No such carrier equality is needed or claimed.

## 4. Exact interpolation interface and completeness quantifiers

The source theorem in INTERPOLATION12 Section 6 states:

> Let A0>1 be even, Delta=A0^2-1, R=3 modulo 4,
> c=psi_A0(R)>0, and c=R modulo 4. For every prescribed positive N
> there is one positive strong pair I,f with 4N c^2|I such that,
> for this same fixed pair, every residue class modulo I contains
> an integer T_old satisfying the auxiliary Pell norm with
> V=f^2(c-R+4I*T_old)-c.

These hypotheses hold for the parent's canonical native witnesses.
A0=a+2 is 2 modulo 4, and the odd-index recurrence gives c=R
modulo 4. The canonical first norm supplies positive tau with
Dt=tau^2. Choose joint guard t and positive Pell-guard ordinate s
first. Apply the theorem with **N=s*tau**. It gives one fixed
I,f with 4s*tau*c^2|I. Set

```
U=I/tau, r=I/(s*tau*c^2).
```

They are positive integers and U=s*r*c^2. The strong pair is fixed
before the requested residue is selected.

The canonical main projection gives integer kappa=K/H. Intersectivity
of pi supplies a residue a modulo |U| with pi(a+kappa)=0 modulo U.
Apply the fixed-pair interpolation theorem to the old residue
**tau*a modulo I**. It gives

```
T_old=tau*a+I*h=tau*(a+U*h).
```

Thus T=T_old/tau is an integer and T=a modulo U. This proves that
every residue of the new T modulo U is attained. It does not divide
an arbitrary T_old by tau. Now

```
Ac/S=pi(T+kappa)/U in Z.
```

The new strong and auxiliary kernels agree exactly with the fixed
source witness. In the rational chart choose
n=Ac/S+3f*tau+9g+y-V; in the integral chart choose
n=Ac/S+3f*tau+9g+delta*y-delta*V. Both are unrestricted integers,
and a conjugate factor vanishes. No positivity bound for n is needed.

The quantifier order is outer data and tau; t and s; one strong pair
from N=s*tau; intersective residue modulo U; old auxiliary residue
tau*a modulo I and its T_old; new T; and finally n.

## 5. Recheck of the interpolation theorem for the new modulus

The source proof permits every positive N, with no hidden coprimality
condition. It uses a Pell matrix period modulo 4N c^2. For the
resulting I=psi_A0(m), f=chi_A0(m), the period modulo f^2 is
lambda=4mf. The source valuation bound v_p(I)>=v_p(m) implies
gcd(lambda,4I^2)|4I. Thus the CRT conditions

```
L=R mod lambda,
L=R-4I*a_old mod 4I^2
```

are compatible for every integer a_old, including a_old=tau*a.
The odd-index polynomial identities give the auxiliary V modulo f^2
and modulo 4I^2. Division by 4I*f^2 then gives exactly
T_old=a_old modulo I. No inverse of tau is used.

## 6. Conclusion and artifact boundary

The new equations have integer zeros exactly when a finite ZFC
refutation exists, through the accepted coherent signed native
calibration. Negation gives the ordinary ZFC-provable
unsolvability/Con(ZFC) equivalence. The small weights are licensed by
mod-3 separation; the period and residue argument licenses the changed
strong and auxiliary coordinates. No bounded numerical search is used
in these implications.

Before publication the literal graphs require independent gate/count,
finite identity, exact degree, authentic coefficient, deterministic
rebuild, and packaging checks. Those checks are separate from this
unbounded semantic proof.
