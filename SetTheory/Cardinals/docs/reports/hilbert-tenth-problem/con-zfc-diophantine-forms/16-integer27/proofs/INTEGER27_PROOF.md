# A polynomial in 27 unrestricted integers

This note combines the signed-domain theorem in package 14-integer29 with
the three-root resultant in package 09-combined13. The new denominator
argument permits all the signs required by package 14. An even weight and
an odd primitive element preserve the canonical completeness witnesses.
The companion improved-weight proof establishes the smaller weight used here.

## Fixed coefficients and inherited interface

Use one complete authentic coefficient tuple `(beta,K0,MC,MFsrc)` of the
blank K215 native-window compiler; `MFsrc` is the shifted source mask.
The delivered default is the pruned 5,268-tile tuple in
`../compiler/pruned_t4_constants.json`. Its ordinary compiler contract
and the required odd-rank, odd-multiplier, square-scale canonical
completeness are proved in `PRUNED_T4_PROOF.md` and independently reviewed
in `COEFFICIENT_TRANSFER_REVIEW.md`. The original package-06 tuple is a
separate valid alternative, never a source for splicing individual ports. All claims here are ordinary proofs
formalizable in ZFC, not new Lean/Rocq builds.

The inherited signed-domain theorem states that the normalized six-factor
polynomial has a zero exactly when K215 halts, if

`J,F,alpha,z,s,eta,zeta > 0`,

`i=2r_i+1`, `w=u^2`, and `f,h,T,tau,y,gamma,r_i,u` are unrestricted
integers. It proves existence completeness with actual positive witnesses
having odd `i`, square `w`, odd canonical rank `R`, and odd `y`.

The following construction removes `f,tau,y` and introduces one integer
`r_t`. This reduces 29 unrestricted integers to 27.

## Literal polynomial recipe

There are seven positive intermediate coordinates

`J,F,alpha,z,s,eta,zeta`,

and six unrestricted coordinates

`h,r_i,T,u,gamma,r_t`.

Replace each of the seven positive intermediate coordinates `x` by

`Pos(x0,x1,x2) = x0^2+x0+x1^2+x2^2+1`.

This is a positive, surjective polynomial map from Z^3 to Z_{>0}; the
standard three-square proof is recalled below. Set

```
i=2r_i+1, w=u^2, t=2r_t+1,
q=beta J+1, Cw=q-F-alpha, X=wq, Y=sq^3, E=XY,
k=eta+zeta, c=kY+eta, a=E+Y, A0=a+2,
H=4a+3, Delta=a^2+H,
Dmain=X+ac+gamma H,
R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MFsrc)J,
N1=Dmain^2-Delta c^2,
Nk=k-hE-R,
Nt=(K0+w)Cw+q-F-z(q-1).
```

For the root component define

```
ell=E kY,
A=1+ell(ell+k), I=i c^2,
D=1+Delta I^2, Q=Delta(D-1), d=Q-1,
v=cT, z0=c+RD,
P0=Q D v^2, Z0=Q z0^2, e=P0+Z0-1,
M=2(I^2+v^2),
L=d t^2, N=d M^2 A, C=L+N-e,
U=C^2+4(P0 Z0-LN),
Res=U^2-16 C^2 P0 Z0.
```

The proposed single polynomial is

`P27 = N1 Nk Nt (1+Res)-1`.

All displayed abbreviations are substituted polynomial expressions,
not additional unknowns or quantifiers. Four equivalent equations are
`N1=Nk=Nt=1`, `Res=0`.

## 1. Units, zero-scale exclusion, and the weak bootstrap

At a zero of P27 every displayed factor is an integer unit. Since
`Delta=a^2+4a+3` is 0 or 3 modulo 4, `N1` cannot be -1. Also `Res` is a
square modulo 4, so `1+Res` cannot be -1. Therefore

`N1=1`, `Res=0`, `Nk=Nt=epsilon` for epsilon in {1,-1}.

Initially `w>=0`, `Y,k,c,a>0`. If `w=0`, then `X=E=0`, `a=Y`, and
`Dmain=ac+gamma H`. Reduction of the main norm modulo H gives 0=1
modulo H, impossible because H>1. Thus w>0 and X>=q>=16.

The inherited weak transport argument uses only `z,F,alpha>0` and
`Nt` being a unit; it gives `Cw>=0`. The authentic mask bounds then give

`3q+1<R<q^4-2`, `E>=q^4>R+2`, `a>R+2`, `Y>=q^3>=4096`.

The construction has `i` odd, so `I!=0`, `I^2>=c^4>1`, `D>1`, and
`Q=Delta^2 I^2>1`. Hence d>0, M>0, and t!=0.

## 2. The main Pell index is at least three, even for signed gamma

The main norm, with c>1, gives an index p>=2 such that

`c=psi_A0(p)`, `|Dmain|=chi_A0(p)`.

The standard integer-coordinate Pell classification is valid for
Delta=A0^2-1. Suppose p=2. Then

`c=2A0`, `D0=chi_A0(2)=2A0^2-1`, `D0-ac=H+4`.

If Dmain=D0 then X=4 modulo H. But 16<=X<a<H, a contradiction.
If Dmain=-D0, use

`(D0-ac)(D0+ac)=1+Hc^2`.

Modulo H this gives `4(D0+ac)=1`, hence `4X=-1` modulo H. This is
impossible because `0<4X+1<H`, as a=(X+1)Y>X. Consequently p>=3 and

`c>=4A0^2-1>3A0^2`.

This proof uses no first-norm root, no positivity of h or gamma, and no
decoded computation. It is therefore available before reconstruction.

## 3. Strict nonvanishing of C

Since `c<k(Y+1)`, the preceding inequality implies

```
A>k^2 X^2 Y^4
 >9 A0^4 E^2 (Y/(Y+1))^2
 >=(144/25) A0^4 E^2
 >4(R+1)^2 A0^4.
```

Here Y>=4 and E>R+2. Also

`D<A0^2 I^2`, `c<I^2`, `z0<(R+1)A0^2 I^2`.

For M0=I^2+v^2, the inequalities

`M0^2>=I^4`, `M0^2>=4 I^2 v^2`

give `A M0^2>4 z0^2` and `A M0^2>4 D v^2`; the latter is automatic
when v=0, since its right side is zero. Averaging gives

`A M0^2>2(Dv^2+z0^2)`.

The selected M=2M0 satisfies the same strict inequality. As
`d=Q-1>=Q/2`, we get

`d A M^2>Q(Dv^2+z0^2)=e+1`.

Therefore `C=d t^2+d M^2 A-e>0`.

## 4. The missing denominator T is automatically nonzero

One must not divide by T before ruling out T=0. A useful independent
bound is

```
Q-z0=(Delta-R)D-Delta-c
     >=D-Delta-c
     =1+Delta(I^2-1)-c>1.
```

Thus `1<z0<Q-1`. Suppose T=0. Then v=P0=0, and Res=0 gives U=0.
Since U=C^2-4LN, the rational number

`tau=C/(2dtM)`

satisfies tau^2=A. A rational square root of an integer is integral.
Set y=t-Mtau, also integral. Substitution gives

`Q z0^2-(Q-1)y^2=1`.

But this implies `(Q-1)(y^2-z0^2)=z0^2-1>0`, so |y|>=z0+1 and

`(Q-1)(2z0+1)<=z0^2-1`.

That is impossible for Q-1>z0>1. Hence T!=0 on every zero.

## 5. Recover all three deleted integer roots

Put `B=2Q v z0`. We now know B!=0 and C>0. The exact identity

`Res=U^2-D(2CB)^2`

gives the rational square root `f=-U/(2CB)` of D. Thus f is an integer.
Moreover

`(C+Bf)^2=4d^2 t^2 M^2 A`.

Hence

`tau=(C+Bf)/(2dtM)`, `y=t-Mtau`

are integers and tau^2=A. Expansion gives

```
d y^2=e-Bf=Q(vf-z0)^2-1,
f^2=1+Delta i^2 c^4,
vf-z0=c(Tf-1)-R f^2.
```

These are exactly the first Pell norm, normalized strong equation, and
auxiliary norm of the inherited signed construction. Every restored root
may be signed; package 14's signed-domain theorem permits these signs.
The other three factors are unchanged and Nk Nt=1, so the normalized
six-factor product is zero. Its soundness theorem yields K215 halting.

## 6. Completeness and the parity choice

If K215 halts, use package 14's canonical normalized witness. It has
positive original coordinates, odd i, square w, and odd final rank R.
Its auxiliary y is `psi_rho(R)`, where rho is the auxiliary Pell base.
The Pell recurrence modulo two gives `psi_rho(n)=n mod2`, so y is odd.

Evaluate M=2(I^2+v^2) at that witness and set `t=M tau+y`. This t is
odd, hence it equals 2r_t+1 for an integer r_t. The root identities give
Res=0. All three retained factors equal one, so P27=0. This proves the
reverse existence implication. The parity restriction on t adds no
unjustified condition to canonical completeness.

## 7. Variable count, exact degree, and charged circuit size

There are `7*3+6=27` unrestricted integer variables. The function Pos is
surjective because Legendre's theorem represents 4n-3 as three squares
for every n>=1; modulo four, exactly one is odd and two are even. Writing
them as `(2x+1)^2,(2y)^2,(2z)^2` gives
`n=x^2+x+y^2+z^2+1`.

The circuit uses 139 binary arithmetic operations: 84 for the improved
13-root circuit, one doubling of M, two operations for odd i, one for
square w, two for odd t, and 49 for seven Pos substitutions. This counts
multiplication by every fixed numeral. The four-equation form uses 133.

Before the Pos substitutions, assign weight two to
`J,F,alpha,z,s,eta,zeta,w` and weight one to `h,i,T,gamma,t`.
The resulting exact degree table is

| Expression | Degree |
| --- | ---: |
| q,X,Y,E,k,c,a,Delta | 2,4,8,12,2,10,12,24 |
| R,I,A,D,Q,v,z0 | 8,21,44,66,90,11,74 |
| P0,Z0,e,M,L,N,C | 178,238,238,42,92,218,238 |
| P0 Z0,LN,U,Res | 416,310,476,952 |
| N1,Nk,Nt | 35,13,4 |
| P27 | 1004 |

Here C has the unique top term -Z0, U has unique top term C^2, and Res
has unique top term U^2. In N1 the terms a^2c^2 cancel; its unique
highest term is `2ac gamma H`, of degree 35. The highest terms of Nk
and Nt have degrees 13 and 4 and are nonzero. Polynomial rings have no
zero divisors, so the product degree is exactly 35+13+4+952=1004.

The disjoint Pos substitutions preserve nonzero highest forms: setting
their second and third arguments to zero reduces them to injective
monomial substitutions `x -> x0^2`. The odd affine substitutions have
nonzero leading coefficient, and w=u^2 is likewise injective. These are
uniform degree proofs for every authentic coefficient tuple beta>0.

## 8. Simpler 28-integer fallback

Package 09's two-root merger needs only t!=0 to replace tau and y by one
coordinate. In package 14's canonical witness, the first root tau is
1 modulo 4 (its Pell base is 1 modulo 4), and auxiliary y is 3 modulo 4
(rho is odd and R=3 modulo 4). Hence t=tau-y is 2 modulo 4. Set
`t=2(2r_t+1)` and use the package-09 ordinary two-root merger unchanged.
This gives 28 unrestricted integers, with a simpler reconstruction but
less variable reduction. The 27-variable polynomial above is the main
recommendation; the fallback is not needed for its proof.

## Evidence boundary

The new result is an explicit polynomial recipe and a proof of existence
equivalence, conditional only on the cited established compiler and
signed-domain theorems. It does not assert a new universal minimum,
does not supply an accepting K215 computation, and does not prove
Con(ZFC). Finite circuit checks corroborate algebra and counts; they do
not replace these infinite-domain arguments or constitute a formal
assistant proof.
