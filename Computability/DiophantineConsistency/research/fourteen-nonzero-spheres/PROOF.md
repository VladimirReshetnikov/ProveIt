# Fourteen positive variables: nonzero spheres at71/80 and72/68

This is the complete ordinary proof for two new equations at the unchanged
CURRENT2011 tuple. Both preserve the entire positive zero set of the actual
fourteen-coordinate Carrier65 polynomial by identity witness maps. The
separate Lean source and finite auditor implement the argument and ledgers;
the maintained page and all accepted predecessors remain unchanged.

## Exact fourteen-variable parent

Use the actual `Carrier65.core` coordinate order
`J,F,alpha,z,f,i,T,s,w,n,eta,zeta,y,gamma`, all strictly positive integers,
with ports `beta,K0,MC,MF_source` and beta positive. MF_source is shifted
by beta exactly once. The scalar `b=beta*J` remains present in q, rank
and transport. In contrast to the thirteen-variable carrier, the strong
seed here uses **i**, not b*i; y is an independent positive coordinate.

Define

```text
b=beta*J, q=b+1, C=q-F-alpha,
X=w*q, Y=s*q^3, E=X*Y, k=eta+zeta, ell=E*k*Y,
c=k*Y+eta, a=E+Y, H=4*a+3, Delta=a^2+H,
D=X+a*c+gamma*H,
R=(b*(q-F)+alpha)*(q^2-1)+(MC+q*MF_source)*J,
tau=E*n+k-R, V=f^2*(c*T-R)-c,
P=tau^2-ell*(ell+k), Q=D^2-Delta*c^2,
W=(K0+w)*C+(q-F)-z*b,
Z=f^2-Delta*(i*c^2)^2,
Theta=Delta*(f^2-1), U=Theta*(V^2-y^2)+y^2.
```

Here Z is the normalized strong factor, not the displayed Carrier65 Z.
With S=i*Delta*c^2, that displayed factor is Delta*Z and its auxiliary
factor is `Uold=S^2*(V^2-y^2)+y^2`. The accepted scaled replacement is
`p66=Delta*(P*Q*U*W*Z-1)`. `CarrierScaledAuxiliary118.positive_zero_sets`
already proves its exact positive-zero equivalence to the actual
Carrier65 polynomial. Since Delta=(a+2)^2-1>0, mathematical cancellation
gives the normalized product equation without introducing a circuit
division. In particular this is the same fourteen-coordinate normalization,
not a substituted thirteen-coordinate equation or a new native tuple.

## A norm cannot vanish: explicit ordinary descent

For integers A>=2 and y!=0, `x^2-(A^2-1)*y^2 != 0`.
Otherwise choose a solution with minimum positive |y| and replace x,y by
their absolute values. Equality and positivity imply

```text
(A-1)*y < x < A*y.
```

Indeed `(A-1)^2 < A^2-1 < A^2`; multiplication by y^2 preserves both
strict inequalities. Set `y'=A*y-x` and `x'=A*x-(A^2-1)*y`.
Then 0<y'<y, and direct expansion preserves the zero norm. Replacing
x' by its absolute value gives a smaller positive second coordinate,
contradiction. This is an integer descent, not a rational-square oracle.

Apply this before assuming any zero equation:

- Let m=E*Y>=2. The exact identity
  `4*P=(2*tau)^2-((2*m+1)^2-1)*k^2` and k>0 imply P!=0.
- With A=a+2>=3 and c>0, the same lemma gives Q!=0.
- With that A and i*c^2>0, it gives Z!=0.
- To show U!=0, split the **positive integer** f into f=1 and f>=2.
  If f=1, Theta=0 and U=y^2!=0 because the coordinate y is positive.
  If f>=2, Delta>0 implies Theta>=3. The exact identity
  `4*Theta*U=(2*Theta*V)^2-((2*Theta-1)^2-1)*y^2`
  and A=2*Theta-1>=2 show U!=0. No sign of V is needed.

The last argument depends on the actual fourteen-variable positive y.
It must not be silently transferred to a signed carrier abbreviation.
These four nonzero statements need only beta>0 and the positive coordinates;
they assume no norm equation, native word, occupation, rank bound, C sign,
or sign of W. The current `ConsecutivePell.norm_ne_neg_one` supplies a
different negative-unit lemma, not this new zero-norm lemma. The new
`NearSquareNormZero.norm_ne_zero` implements this descent explicitly.

## Two complete equations and both identity maps

The proposals are

```text
A71 = (P*Q)^2 + (U*W-1)^2 + Z^2 - 2,
B72 = P^2 + U^2 + Z^2 + (Q*W-1)^2 - 3.
```

For A71=0, P*Q and Z are nonzero integers, so each raw square is at
least one. Nonnegativity of the middle square forces
`(P*Q)^2=Z^2=1` and U*W=1. The existing unconditional exclusions P!=-1,
Q!=-1 and Z!=-1 give P=Q=Z=1. The strong equality now gives
`Theta=S^2`; therefore `ShortSystem.square_aux_ne_neg_one` excludes
U=-1. Since U*W=1, it follows that U=W=1.

For B72=0, P,U,Z are nonzero integers, so their three squares are each
at least one. Hence `P^2=U^2=Z^2=1` and Q*W=1. The same negative-unit
exclusions give P=Z=1, then U=1 after Theta=S^2, and finally Q=W=1.
No unconditional exclusion of U=-1 or W=-1 has been asserted.

In either case P=Q=U=W=Z=1 implies the normalized product vanishes;
Z=1 identifies U with Uold and the actual Carrier65 norm theorem gives
the original polynomial zero. Conversely every actual positive Carrier65
zero has P=Q=Uold=W=Z=1. Again Theta=S^2 gives U=Uold, so both proposed
polynomials vanish on precisely those same fourteen coordinates. The two
maps are the identity on the **entire** positive zero sets. They require
no canonical-witness restriction or change of the fixed ports.

The source-bound sign lemmas are `Carrier65.first_shape`,
`firstParameter_ge_two`, `delta_shape`, `strong_scale`,
`value_zero_iff_norms`, `ConsecutivePell.norm_ne_neg_one`,
`ShortEquation.strong_ne_neg_one`, and
`ShortSystem.square_aux_ne_neg_one`. The external current-port endpoint
composes the proved positive maps with
`CarrierScaledAuxiliary118.no_current_positive_zero_iff_conZFC` or the
literal Carrier65 endpoint. No internal HA or ZFC derivation follows from
this ordinary argument.

## Manual complete paid ledger

All fixed constants are integer leaves. Every row below is one paid binary
operation; squares are multiplications. This ledger is independently compared with both
complete materialized operation arrays by the standalone auditor. Rows1–51 are the exact current65 parent prefix,
with names P,Q,W substituted for its N0,N1,Nt. The common62-row prefix is:

```text
 1 b=beta*J                 2 q=b+1
 3 q2=q*q                   4 q3=q2*q
 5 X=w*q                    6 Y=s*q3
 7 E=X*Y                    8 k=eta+zeta
 9 kY=k*Y                  10 ell=E*kY
11 c=kY+eta                12 a=E+Y
13 four_a=4*a              14 H=four_a+3
15 a2=a*a                  16 Delta=a2+H
17 ac=a*c                  18 main_base=X+ac
19 gammaH=gamma*H          20 D=main_base+gammaH
21 c2=c*c                  22 Dc2=Delta*c2
23 D2=D*D                  24 Q=D2-Dc2
25 qF=q-F                  26 C=qF-alpha
27 gap_product=b*qF        28 gap=gap_product+alpha
29 q2minus1=q2-1           30 rproduct=gap*q2minus1
31 qMF=q*MF_source         32 maskfactor=MC+qMF
33 mask=maskfactor*J       34 R=rproduct+mask
35 En=E*n                  36 tau_partial=En+k
37 tau=tau_partial-R       38 tau2=tau*tau
39 ell_plus_k=ell+k        40 first_product=ell*ell_plus_k
41 P=tau2-first_product    42 Kw=K0+w
43 transport=Kw*C          44 transport_partial=transport+qF
45 zb=z*b                  46 W=transport_partial-zb
47 f2=f*f                  48 cT=c*T
49 L=cT-R                  50 f2inner=f2*L
51 V=f2inner-c             52 i2=i*i
53 i2Dc2=i2*Dc2            54 strong_term=i2Dc2*c2
55 Z=f2-strong_term        56 V2=V*V
57 y2=y*y                  58 square_gap=V2-y2
59 f2minus1=f2-1           60 Theta=Delta*f2minus1
61 auxiliary=Theta*square_gap
62 U=auxiliary+y2
```

Rows1–51 have27 multiplications,15 additions,9 subtractions; rows52–62
have7 multiplications,1 addition,3 subtractions. Thus the prefix costs
62=34M+16A+12S. The already required Dc2 is shared by Q and Z;
neither it nor c2 is charged twice. The old S/S²/scaled-f² producers are
removed, not retained as dead gates. The final two schedules are:

```text
A71: 63 PQ=P*Q              64 UW=U*W
     65 rUW=UW-1            66 PQ2=PQ*PQ
     67 rUW2=rUW*rUW        68 Z2=Z*Z
     69 sum1=PQ2+rUW2       70 sum2=sum1+Z2
     71 output=sum2-2

B72: 63 QW=Q*W              64 rQW=QW-1
     65 P2=P*P              66 U2=U*U
     67 Z2=Z*Z              68 rQW2=rQW*rQW
     69 sum1=P2+U2          70 sum2=sum1+Z2
     71 sum3=sum2+rQW2      72 output=sum3-3
```

The manual totals are A71=39M+18A+14S and B72=39M+19A+14S.
Every row and all fourteen coordinates/four ports feed the output.
The standalone auditor separately checks these counts and complete liveness.
No omitted division, free square or right-hand-side change is included.

## Exact degree argument and comparisons

Let `q0=beta*J`, `k0=eta+zeta`, and `C0=q0-F-alpha`. The shared factor
leaders, including the retained main-norm cancellation, are

```text
P0 = -w^2*s^4*k0^2*q0^14                         degree22
Q0 = 8*gamma*w^2*s^3*k0*q0^11                    degree18
U0 = w^2*s^4*k0^2*q0^14*f^6*T^2                 degree30
W0 = w*C0-z*q0                                  degree2
Z0 = -i^2*w^2*s^6*k0^4*q0^20                    degree34.
```

Only (PQ)^2 reaches degree80 in A71, whose complete leader is
`64*gamma^2*w^8*s^14*k0^6*q0^50`. The coefficient of
`J^50*eta^6*gamma^2*w^8*s^14` is64*beta^50, nonzero at the actual beta.
The other two square degrees are64 and68. Only Z² reaches degree68 in
B72, whose complete leader is `i^4*w^4*s^12*k0^8*q0^40`; its selected
`J^40*eta^8*i^4*w^4*s^12` coefficient is beta^40. The other square
degrees are44,60,40. The standalone auditor independently checks every gate leader and the
complete coefficients. The Lean zero-set proof is separate from this finite
degree audit; no Lean totalDegree theorem is asserted.

The two leads are incomparable with each other. Within the tabulated
low-variable frontier, neither is dominated by 14/65/150,14/66/118,
13/71/128,13/72/124,13/74/122, or13/75/96: an extra variable is traded
for lower operation count and degree relative to the thirteen-variable
sphere. A71 would dominate the historical15/73/80 point; B72 would
dominate15/75/68. The older15/76/64 point still has lower degree. These
comparisons do not assert a global minimum or an exhaustive survey of
all representations/metrics.

## Pins and proof boundary

- Current65 whole graph `candidates/one-page-padding-staircase-carrier65-2011/polynomial.json`:
  `f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e`.
- `Carrier65.lean`:
  `be2f2cb6833d190818541a57bb9b7c148c5975864d6af518f511b67f80fb1154`.
- `CarrierScaledAuxiliary118.lean`:
  `2e222efd3b40626e6734fe30e5b7239fb7a7abd5fd9c14bee8e4a238c237c620`.
- `ConsecutivePell.lean`:
  `2ca72494501464fe29aeef854fdbf585b0aba28ba0687df4a6aa8d8095699d92`.
- `ShortSystem.lean`:
  `a9d50c6d8268df4d854d056c83995b3e0547c483fd800993471b2c718201d44a`.

`NearSquareNormZero.lean` proves the generic descent, and
`CarrierNonzeroSpheres.lean` proves the four unconditional nonzero facts,
conditional negative-unit exclusion, both whole positive-zero maps, actual
polynomial evaluations and both current-port external ConZFC endpoints.
The separate standard-library auditor binds both complete schedules, all
gate leaders and all CURRENT2011 integers without importing project code.
The historical66/118 finite packet uses2501 ports; it supplies algebraic
context only. Every new coefficient copy is instead bound to the current
2011 graph's exact47313-byte tuple. Validation commands, source/object pins
and author/independent roles belong in the final receipts. Neither these
external Lean equivalences nor the finite audit establish an internal HA,
PA or ZFC derivation, actual consistency, or global optimality.
