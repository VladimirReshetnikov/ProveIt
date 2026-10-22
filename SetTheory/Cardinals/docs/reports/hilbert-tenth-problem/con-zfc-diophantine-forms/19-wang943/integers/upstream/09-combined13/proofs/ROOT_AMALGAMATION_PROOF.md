# Root amalgamation for the fixed blank K215 slice

This note first derives its formulas for the inherited four-port arithmetic interface of `06-blank67`; references below to that package's exact coefficients describe this initial derivation. The accompanying report proves transfer to the new four-site recipe, with the final default binding in `../COEFFICIENT_BINDINGS.json` selecting the package-root recipe `compiler/tshape_constants.json` and its shifted MF mask.

All fixed numerals are **the four coefficients of package 06-blank67** at
`3b201cdea32d2c816f5f3d20734051f25fd3ef14`. In particular the F mask is
the shifted port. The following proof is ordinary mathematics, formalizable
in ZFC using the inherited compiler/Pell lemmas. It is not a new proof-assistant
certificate. All supplied unknowns are strictly positive integers.

Use package06's common abbreviations

```
q=(B-1)J+1, Cw=q-F-alpha, X=wq, Y=sq^3, E=XY,
k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3, Delta=a^2+H,
Dmain=X+ac+gamma H, Lfirst=E(kY),
R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MFsrc)J,
N1=Dmain^2-Delta c^2,
Nk=k-hE-R,
Nt=(Kconstant+w)Cw+q-F-z(q-1).
```

The files use descriptive register names; the displayed mathematical
abbreviations are substituted polynomials, not additional unknowns.

## 1. Fourteen unknowns, five equations, degree 72

Retain f and remove tau,y; supply one positive t. Define

```
A=1+Lfirst(Lfirst+k), I=ic^2, K=Delta(f^2-1),
V=c(Tf-1)-Rf^2, d=K-1, e=K V^2-1,
L=d t^2, N=d A, u=L+N-e,
Res14=u^2-4 L N.
```

The equations are `N1=Nk=Nt=1`, `I^2=K`, and `Res14=0`.
The fully charged comparison circuit has 67=38M+29A operations. A single
sum of squares has 81=43M+38A operations and degree144. These degrees are
exact: A has degree22, K degree14, u degree36 with leader K_top A_top,
so Res14 has degree72 while 4LN has degree52.

At any solution, K=I^2>1, hence d>0. Put

```
tau = u/(2dt), y=t-tau.
```

Res14 gives tau^2=A. A rational number with integral square is an integer,
so tau and then y are integers. Substituting the defining linear relation
gives d y^2=e. Thus the first and auxiliary norms are restored exactly.
Neither root is zero: A>1; if y=0 then K V^2=1, impossible since K>1.
Taking absolute values of tau,y changes neither equation. This produces
a positive solution of the ordinary15 system in LOW_DEGREE_PROOF.md.
Conversely put t=tau+y for a positive solution of that system.

### Single product of degree121

Define Ns=1+I^2-K and

```
P14=N1 Nk Nt Ns (1+Res14)-1.
```

Its literal circuit has76=42M+34A operations and degree
18+7+2+22+72=121. At any zero, all five factors are integer units.
Delta is0 or3 modulo4, so N1 cannot be-1. Also
K=Delta(f^2-1) is0 or1 modulo4; Ns=1+I^2-K is never3 modulo4.
Hence Ns=1 and K=I^2>1. Since Res14 is a square modulo4,
1+Res14 cannot be-1; it is1. Restore signed tau,y as above and replace
them by their positive absolute values. The resulting tuple satisfies
the ordinary15 six-factor product equation. Its proof in
LOW_DEGREE_PROOF.md (including the Cw=0 bootstrap and index-sign recovery)
then forces Nk=Nt=1 and proves acceptance. Completeness is immediate.

No signed-f or signed-T extension is needed for this fourteen-variable
construction.

## 2. Thirteen unknowns by a weighted primitive element

Remove f,tau,y and supply one positive t. Keep the other twelve unknowns
`J,F,alpha,z,h,i,T,s,w,eta,zeta,gamma`. Define

```
A=1+Lfirst(Lfirst+k),
Q=(Delta i c^2)^2, D=1+Delta i^2 c^4,
v=cT, z0=c+RD, d=Q-1, e=Q(Dv^2+z0^2)-1,
M=D+v^2,
C=d(t^2+M^2 A)-e,
B=2Qvz0,
U=C^2+D B^2-4d^2 t^2 M^2 A,
Res13=U^2-D(2CB)^2.
```

Use four equations `N1=Nk=Nt=1`, `Res13=0`. The weight M is essential:
the unweighted t=tau+y resultant can have a zero denominator and does
not by itself prove the eliminated roots are rational.

### Positivity of the denominator

The same argument also works if Nk=Nt are equal signs in {+1,-1}.
Weak transport forces Cw>=0. Package06's actual mask bounds give

```
q>=16, 0<R<q^4-2, E>=q^4>R+2.
```

Consequently k=R+epsilon+hE>R, c<k(Y+1), and Y>=q^3>=4096.
Write U0=XY^2. Then A=1+k^2 U0(U0+1), so

```
A > k^2 Y^4 > 8 k^2((Y+1)^2+1) > 8(c^2+R^2).
```

The middle inequality holds for Y>=4: (Y+1)^2+1<=13Y^2/8 and
Y^4>=16Y^2>13Y^2. Also D>1, z0=c+RD>0, and

```
M^2=(D+v^2)^2 >= 4Dv^2,
M^2 >= D^2,
z0^2 <= 2D^2(c^2+R^2).
```

Splitting A M^2 into two equal terms, the first exceeds 4Dv^2 and the
second exceeds 2z0^2. Hence A M^2>2(Dv^2+z0^2). Since Q>=2 and
d=Q-1>=Q/2,

```
d A M^2 > Q(Dv^2+z0^2)=e+1.
```

Therefore C>0. Also B>0, d>0, t>0, M>0. All subsequent divisions are
proof-only by established nonzero integers.

### Recovering all three roots

From Res13=0 put f=-U/(2CB). Then f^2=D, so f is a nonzero integer.
The identity

```
(C+Bf)^2=4d^2 t^2 M^2 A
```

follows by expanding and using U+2CBf=0. Thus

```
tau=(C+Bf)/(2dtM), y=t-M tau
```

satisfy tau^2=A and are integers. Expansion gives

```
d y^2=e-Bf=Q(vf-z0)^2-1.
```

The strong norm f^2-Delta i^2 c^4=1 holds because f^2=D. Since
vf-z0=c(Tf-1)-R f^2, this restores exactly the normalized strong and
auxiliary equations, provisionally with signed f,tau,y. Again tau,y
are nonzero and may be replaced by their absolute values.

For f<0 replace f,T simultaneously by -f,-T. All expressions in the
retained arithmetic depend on f only through f^2 and Tf. This gives a
positive f with a possibly signed auxiliary quotient T.

### Signed-quotient soundness, with no input bridge

This last domain extension must not be silently replaced by the ordinary
positive-T compiler theorem. The needed proof is explicit in
`complete84_signed_quotient_absorption.md`, section2, followed by
`complete84_signed_quotient_soundness_scout.md`, sections2-4. It applies
here with the package06 bootstrap bounds just established:

* N1=1 classifies c=psi_(a+2)(p), Dmain=chi_(a+2)(p).
* The restored first norm classifies k=2psi_(2XY^2+1)(n).
  The index congruence gives n>=(R-1)/2 and p>n; growth gives c>2p.
  Since k>R and Y>=4096, c>2R.
* The normalized strong equation and strong divisibility give
  f=chi_(a+2)(m), pc|m and m>2p, without a sign premise on T.
* Classify the absolute auxiliary root, retaining its sign. The two
  congruences V=-c modulo f and V=-R modulo c imply R=+/-p modulo c.
  Bounds 0<R,p<c/2 give p=R. This step does not require V>0 or positive
  restored quotient coordinates.
* E>R+2 excludes first-index wrap, and the Pell ratio excludes Nk=-1.
  Thus Nk=Nt=1 and Cw>0.
* The lower Pell-ratio estimate and the main-root congruence recover
  X=2^R. The retained factor q in X makes q dyadic; R>3q restores
  q^3|X. The half-binomial extraction and exact population inversion
  use no sign of T or V and recover the native masks.
* Apply package06's blank-input native-window proof, whose inputs are
  these masks, powers and transport identity. It does not inspect the
  deleted numerical-input bridge or any auxiliary-root sign.

This proves the represented blank halting condition. One can additionally
recover T>0 using the valid mask congruences and both unsquared auxiliary
congruences as in the scout's section5; that extra conclusion is not
needed to decode a blank tableau here. Section6 of that scout concerns
the old ordinary-input bridge and is not used.

Conversely start with any positive normalized package06 solution. Its
f,tau,y satisfy the displayed squared equations. Choose t=M tau+y>0.
Then C+Bf=2dtM tau and U+2CBf=0, so Res13=0. Thus the four-equation
construction and blank K215 halting are equivalent in existence.

### A shorter shared evaluator

The emitted circuit uses

```
P0=Q Dv^2, Z0=Q z0^2, e=P0+Z0-1,
L=d t^2, N=d M^2 A, C=L+N-e,
a0=P0 Z0, b0=LN,
U=C^2+4(a0-b0), Res13=U^2-16C^2 a0.
```

This is exactly the same polynomial because D B^2=4P0 Z0.
The four-comparison system costs78=46M+32A operations, and its sum of
squares costs89=50M+39A operations. Their maximum degree and degree are
544 and1088, respectively.

### A single product with 84 operations

Set

```
P13=N1 Nk Nt (1+Res13)-1.
```

It costs84=49M+35A operations. At a zero all four factors are units.
Because Res13=U^2-16C^2a0, its residue modulo4 is a square, so its
guard cannot be-1. Hence Res13=0. The main norm cannot be-1; Nk,Nt
have a common sign. The denominator argument above explicitly allowed
these signs and therefore applies without circularity. Signed rank
then forces the two signs positive, as above. This proves the same
halting equivalence as the system.

### Exact degrees

With every supplied unknown of degree1 and fixed numerals of degree0:

| Expression | Degree |
|---|---:|
| c, a, Delta, R | 5,6,12,4 |
| A,Q,D,v,z0 | 22,46,34,6,38 |
| P0,Z0,M,L,N,C | 92,122,34,48,136,136 |
| a0,b0,U,Res13 | 214,184,272,544 |

C has the unique leading term from N; U has the unique leading term
from C^2; Res13 has the unique leading term from U^2. Thus these
degrees are exact for every valid fixed coefficient slice. The product
has exact degree18+7+2+544=571: the other three nonzero leading forms
multiply the nonzero fourth power of C's leading form. A polynomial
ring over the integers has no zero divisors. The sum-of-squares degree
is1088 because the resultant is its unique highest-degree residual.

## 3. Reproducibility and comparison

`build_candidates.py` emits every live gate and counts every binary
operation, including constants4 and16. It compares the complete
thirteen-variable expressions with an independently expanded formula on
80 signed assignments and performs two exact modular univariate degree
diagnostics. Uniform degree proofs are the leading-form arguments above;
sampling is supplementary evidence. No accepting K215 run and no full
astronomical Pell witness is claimed.

The script also records package05's simpler f-elimination transplanted
to the inputless slice: fourteen-variable products of degree293 at75
operations, or degree342 at73 operations. These are useful arithmetic
tradeoffs, but the fourteen-variable merger above has much lower degree
at76 operations. None of these constructions establishes a global
minimum or changes the nine-variable existence theorem.

## 4. Optional smaller-degree weight for thirteen variables

One additional arithmetic operation gives a second choice

```
I=ic^2, M=k I^2+T^2,
D=1+Delta I^2, Q=Delta(D-1).
```

The definitions of D,Q are identical to section2. Compute v^2 as c^2T^2;
the resulting source uses the same five gates for I,I^2,D-1,D,Q as the
earlier source used for the two strong roots, their square, D-1,D.
The weight now costs two gates rather than one. All other formulas are
unchanged. Thus the system has79=47M+32A operations, the product has
85=50M+35A operations, and the sum of squares has90=51M+39A operations.

Here is the independent domination proof. Write Aparam=a+2. From the
same weak bootstrap, k=R+epsilon+hE>E, R>3q, and c<2kY. Since X>=16
and Y>=4096, Aparam=E+Y+2<2E. Therefore

```
Lfirst=kEY > Aparam*c/4,
Lfirst>E^2Y>4 Aparam^2.
```

Consequently A> Aparam^2 c^2/16 and A>16 Aparam^4. Also
D<Aparam^2 I^2 because I>1. The selected weight satisfies

```
M^2>=4k I^2 T^2,
M>=k I^2,
z0=c+RD<2k Aparam^2 I^2.
```

The last inequality uses R<k and c<I^2. Since k>R>3q>=48, these
give A M^2>4Dv^2 and A M^2>4z0^2. Adding the halves again yields
A M^2>2(Dv^2+z0^2), proving the same strict C>0 bound. Hence the
whole root-restoration and compiler proof is unchanged.

Now M has degree23, N has degree114, and e has degree122. Thus C has
the unique leading term -e_top, U has degree244, and Res13 has exact
degree488. The single product has degree515 and the sum of squares
degree976. These values are uniformly exact: all top forms just named
are nonzero and the other resultant term has degree458. This is a
small extra arithmetic cost for a lower-degree thirteen-variable form;
the84-operation product remains the cheaper circuit.

