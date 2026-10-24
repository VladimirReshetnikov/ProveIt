# A weaker congruence for twelve unrestricted integer variables

## Scope and exact output

Fix the six literal coefficient payloads of the source34 tuple at ProveIt
commit `84e16e43092614bae262ca59651cb9d77e31a255`. In particular
`beta=2^1064921-1`. Every unknown is an unrestricted integer. The twelve
coordinates are `j,C,z,h,r,v,w,T,c,n,t,s`.

| File | Binary additions/subtractions/multiplications | Exact degree |
|---|---:|---:|
| `integral.json` | 140 | 1040 |
| `rational.json` | 144 | 816 |
| `centered.json` | 147 | 800 |

Each equation has an integer zero if and only if the retained ordinary
native/compiler calibration has a finite ZFC refutation. Thus ZFC proves
that its absence of integer zeros is equivalent to Con(ZFC), using exactly
the named ordinary source calibration of the parent. No new proof-assistant
formalization or global simplicity optimum is claimed. The changes below
are proved independently of the finite circuit checks.

The direct parent is `candidates/scalar-carrier12` at the pinned commit.
Its proof is retained as `source/scalar-parent-proof.md`, together with
`PRIME_TWELVE.md`, `INTERPOLATION12.md`, `signed-quadratic-proof.md`, and
`RESIDUE_AND_DETERMINANT.md`. We use its signed main-index folding before
the main congruence, its general strong multiplier theorem, and its
full-residue interpolation theorem. Their hypotheses are checked in the
order below; no odd strong-multiplier substitution is assumed.

## 1. Front registers and new carrier

The front is the parent's front, without any arithmetic change:

```
J=6j+1, q=beta J+1, W=12w+4, X=qW,
Y=(2v+1)q^3, a=(X+1)Y, H=4a+3, Delta=a^2+H,
F=(K0+W)C-z(q-1),
R=[q(q-F)-C](q^2-1)+(MC+q MF)J,
k=R+1+hXY,
eta=c-Yk, zeta=k-eta,
Ucone=cone_A F, Vcone=cone_B C,
G=Ucone Vcone-(q-Ucone-Vcone)^2,
Pair=G eta zeta-[t^2-G-eta zeta+1]^2,
Dg=(3Pair-4)s^2+1,
I=src^2, Df=1+Delta I^2, Q=Delta^2 I^2, delta=Q-1,
V=Df(c-R+4IT)-c, Cy=QV^2-1,
ell=XY^2, Dt=1+ell(ell+1)k^2.
```

MF is the already shifted source34 coefficient. Let

```
Kstar=X(2X-3c)-2,
z=HT+Kstar,
Phi_H(z)=(z^2+3H^2)(z^3-19H^3),
A=Phi_H(z), S=srH, U=Sn-A.
```

The shorter projector has the exact polynomial identity
`Kstar=2Kold-HXc`, where `Kold=X(X+2ac)-1`.

Write F16(x;a,b,e,d) for the product of all sixteen independent factors
`x +/- sqrt(a) +/- sqrt(b) +/- sqrt(e) +/- sqrt(d)`. This is an ordinary
integer polynomial; the signs and square roots describe its polynomial
identity, not extra unknowns or allowed operations in the output.
Put `a1=9S^2 Df, b1=81S^2 Dt, e1=729S^2 Dg`. The two uncentered forms are

```
P_rat = delta^8 F16(U; a1,b1,e1,S^2 Cy/delta),
P_int = F16(U; a1,b1,e1,S^2 delta Cy).
```

The first expression has been cleared symbolically, so its delivered DAG
also has only integer additions, subtractions and multiplications.

The parent used `S=I H^5`. We use `S=srH`. The missing factor c^2 is recovered
from the strict strip guard, and the missing powers of H are replaced by
an explicit bound using the actual fixed coefficient beta.

## 2. Zero scale, all radicals, and the c=0 branch

Unconditionally, q is even and 2 modulo 3, X is 2 modulo 3,
a is even, H is odd and nonzero, Delta>1, and Q is either zero or greater
than one. Hence delta is never zero. Also

```
H=Delta=0 mod 3,
Df=Dt=1 mod 3,
delta=Cy=-1 mod 3.
```

If S=0 then sr=0, so I=0, Q=0, delta=Cy=-1 and V=-R. All scaled
radicands vanish, and either polynomial equals A^16. But
`A=H^5 pi(T+Kstar/H)`, where `pi(x)=(x^2+3)(x^3-19)`.
The rational argument cannot be a zero: the quadratic has no real zero,
and the cubic has no rational zero. Thus S cannot vanish at a zero of
the final equation. In particular s and r are nonzero. We have not yet
assumed c is nonzero.

Divide a vanishing conjugate factor by S. The four squared radical terms
have 3-adic orders `0,2,4,6+v3(Dg)`, omitting a zero guard term. Every
subset with at least two surviving terms has a unique least order, which
is even. The parent's localization proof consequently excludes every
nonempty signed subsum, including a potentially imaginary guard term.
The multiquadratic automorphism argument forces all four roots rational.
Thus Df, Dt, and Dg have integer roots f,tau,g; the auxiliary rational
root is handled below. This argument is valid at c=0: then I=Q=0,
delta=Cy=-1, and either normalized auxiliary radicand is exactly 1.

Since s is a nonzero integer and Dg=g^2>=0, Pair<=0 would give Dg<=-3.
Therefore Pair>0. The parent's joint positivity lemma yields G>0 and
eta*zeta>0. If c=0, however, `eta*zeta=-Y(Y+1)k^2<=0`.
This contradiction excludes c=0. Now I is nonzero and Q>1. The
adjacent-coefficient Pell descent makes the auxiliary root integral:
`QV^2-(Q-1)y^2=1`. For the integral form, first divide the extracted root
by delta to obtain this rational root, then apply the same descent.
We may finally use the integral conjugate factor to conclude S|A.
This dependency order is essential: c is excluded by the guard before
using any strong-rank theorem that needs a nonzero c.

## 3. What the weak carrier actually proves

Because H divides S, H divides A. Modulo H the homogeneous quintic is
just z^5. Since z=HT+Kstar, we obtain only `H|Kstar^5`.
We do not infer H|Kstar from this divisibility: that inference would be
false for a nonsquarefree H. Instead, H is odd and
`Kstar=2Kold-HXc`, so H divides Kold^5. The next section proves the
required power identity directly from this weaker congruence.

## 4. Height converts fifth-power divisibility into exact vanishing

The parent's absolute Pell-index folding and strict strip bootstrap do
not use H|Kold. They apply now because all their roots and strict guards
have been recovered. They give

```
c = sigma psi_(a+2)(R), sigma in {+1,-1},
R=2u+1, u>=24,
x=|X|, m=|Y|, m > (x-3)^u/2 - 1.
```

The strong multiplier need not be odd. The retained interpolation proof
uses c^2|I to show the main rank divides the strong rank and that |c|
divides the latter; the auxiliary residue gives the same step-down.
These are exactly the hypotheses checked in the parent's Section 4.

Let `D=(sigma X-2^R)(2^R sigma X+1)`. The Pell recurrence and
`4(a+2)=5 mod H` give the same polynomial congruence as in the parent:
`D=2^R Kold mod H`. Only powers of 2 are inverted; H is odd. No division
by 3 modulo H is used. In particular H|Kold^5 implies H|D^5.

Here we exploit the actual fixed coefficient, not a generic small beta.
The integer 6j+1 is nonzero and |12w+4|>=4, so
`x>=4(beta-1)>2^36`. Since |H|>=4(x-1)m-3, the ratio bound implies

```
|H| > 2(x-1)(x-3)^u - 4x + 1 > (x-3)^(u+1).
```

The second inequality follows from `(x+1)(x-3)^u>4x-1`, valid already
for x>=64 and u>=1. Hence `|H|>(x/2)^(u+1)`. Meanwhile

```
|D| <= 2^(2R+2) x^2,
|D|^5 <= 2^(20u+20) x^10.
```

For x>=2^36 and u>=24,
`x^(u-9)>=2^(36u-324)>2^(21u+21)`, because the exponent difference is
`15u-345>=15`. Therefore `(x/2)^(u+1)>2^(20u+20)x^10`, and
`|D|^5<|H|`. The integer multiple D^5 of H must be zero. Its second
factor `2^R sigma X+1` is odd and nonzero, so sigma X=2^R.

The parent's signed main projection now reconstructs d and the integer
main quotient gamma; all remaining signed-kernel rows were unchanged.
Its ordinary native/refutation theorem yields a finite ZFC refutation.
No consistency assumption enters this implication.

## 5. Completeness and the unchanged interpolation order

Start with a finite refutation and the parent's canonical native witness.
Choose the joint positivity t and its nonzero guard Pell witness s.
The inherited theorem fixes one strong pair I,f with 4sc^2|I and permits
EVERY residue of T modulo I, without altering that fixed strong pair.
Set r=I/(sc^2). The canonical main projection gives H|Kold and hence
H|Kstar. Put kappa=Kstar/H.

The intersectivity of pi supplies a residue T with
`I|pi(T+kappa)`. Choose its interpolated auxiliary witness, using the
retained period 4mf and all its compatibility hypotheses. Then

```
A=H^5 pi(T+kappa),
A/S = c^2 H^4 pi(T+kappa)/I is an integer.
```

Choose `n=A/S+y+3f+9tau+27g` for P_rat, or replace y by delta*y
for P_int. One conjugate factor vanishes. Negative or zero values of n
are allowed. A zero guard root (including Pair=1,s=1,g=0) is allowed.
No coprimality of H and I is assumed and no witness is chosen circularly.

## 6. Centering the integral auxiliary root

Use the integer polynomial automorphism `n_old=n+delta V`. This makes
P_int's center `U+L`, where

```
L=S delta V,
N=S^2 delta(1-V^2),
S^2 delta Cy = L^2-N.
```

Eliminating the auxiliary root first turns the two corresponding factors
into `E(W)=W^2+2LW+N`, where
`W=U +/- 3S sqrt(Df) +/- 9S sqrt(Dt) +/- 27S sqrt(Dg)`.
The product of these eight E(W) is the centered polynomial. The inverse
coordinate translation is `n=n_old-delta V`, so its integer zero set has
exactly the same existence statement as P_int.

The evaluator forms `SV=S V`, `L=SV delta`, `N=S^2 delta-L SV`,
then uses `d=L^2-N`, `z=U+L` and the low-degree identity

```
z^2+e1-a1-b1-d = U(U+2L)+N+e1-a1-b1.
```

This removes the cancellation before computing the final norm; the
resulting 147-operation DAG has syntactic degree 800. Its generic
six-variable centered norm identity has all 1,890 coefficients checked
against a separately constructed conjugate product.

## 7. Attained exact degrees and verification boundary

The front degrees are `deg(H)=6`, `deg(I)=4`, `deg(delta)=32`,
`deg(V)=25`, `deg(Cy)=82`, `deg(S)=8`, `deg(A)=35`.
For P_rat, the unique top argument is `delta U^2`, degree 102, and its
eighth power gives 816. For P_int it is `S^2 delta Cy`, degree 130,
and its eighth power gives 1040. For the centered equation the leading
part of each E(W) is 2LU, degree 100, giving total degree 800.

Independent graded-lex leading induction through every actual DAG gate
finds these strictly positive actual coefficients:

```
P_rat: [j^448 w^112 v^112 s^16 r^16 c^32 T^80]
         = 2^944 * 3^560 * beta^448;
P_int: [j^448 w^112 v^112 s^96 r^96 c^160 T^16]
         = 2^848 * 3^560 * beta^448;
P_centered: [j^384 w^96 v^96 s^48 r^48 c^80 T^48]
         = 2^792 * 3^480 * beta^384.
```

Their exponent sums are respectively 816,1040,800. There is no zero
leading coefficient at any gate, so the computation is an exact proof
of degree, not a generic syntactic estimate or a finite numerical sample.
The independent checker binds every displayed front expression in a free
integer polynomial ring, authenticates all six actual coefficient bytes,
checks the entire free four-root norm and the centered substitution, and
rejects deliberately corrupted projector, carrier and norm operators.
These finite algebraic checks complement the universal argument above;
they do not prove the unbounded native/refutation calibration anew.
