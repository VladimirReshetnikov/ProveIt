# Two further corrections: 13/92/90 and 13/97/88

All thirteen unknowns are positive integers, in the exact order
`J,F,alpha,f,i,T,s,w,n,eta,zeta,m,gamma`. The four fixed integer ports are
`beta,K0,MC,MF`; MF is the native current2011 mask shifted by beta once.
Their complete values are unchanged from the accepted thirteen-coordinate
unit sphere: 47,313 raw bytes and 4,230 gzip bytes. There is no new variable,
root, rational coefficient, division, or constraint.

## Complete common polynomial definitions

Use these integer polynomials, with all powers paid by the literal graph:

```
b=beta*J, q=b+1, X=w*q, Y=s*q^3, E=X*Y, k=eta+zeta,
ell=E*k*Y, c=k*Y+eta, a=E+Y, H=4*a+3, delta=a^2+H,
D=X+a*c+gamma*H, C=q-F-alpha, G=(K0+w)*C-F,
R=(b*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J,
tau=E*n+k-R,
P=tau^2-ell*(ell+k), Q=D^2-delta*c^2,
L=c*T-R, V=f^2*L-c,
y=1+4*(b*(m-L*V*G)-G),
U=delta*(f^2-1)*(V^2-y^2)+y^2,
Z=f^2-delta*(b*i*c^2)^2, h=f^2-1.
```

Set W=b*T*G*V and define

```
A90=16*W*(W*h+2*f^2*T*(V*C-b*G*f^2*R)),
A88=16*T^2*V*((b*G)^2*V*h
       +2*f^2*(V*C*(2*b*G-X*C)-(b*G)^2*f^2*R)),
U90=U-A90*(P-1), U88=U-A88*(P-1),
p90=(P*Q)^2+U90^2+Z^2-3,
p88=(P*Q)^2+U88^2+Z^2-3.
```

The exact coefficient identity is
`A88=A90-32*f^2*T^2*V^2*C*(X*C-b*G)`. It is proved by ring normalization
in Lean and independently by the complete cut-polynomial audit. The useful
cancellation `X*C-b*G=(w-b*K0)*C+b*F` lowers this particular expression's
degree. It does not introduce a free operation in either paid graph.

## Entire positive zero sets, with identity witnesses

The accepted unit-sphere equation is `p75=(P*Q)^2+U^2+Z^2-3=0`.
For every positive assignment with beta>0, its established arithmetic
lemmas give P != -1 and Q != -1. No assumption concerning the corrected
auxiliary U90 or U88 is made.

For arbitrary integers P,Q,U,Z,A with P,Q != -1, if
`(P*Q)^2+(U-A*(P-1))^2+Z^2=3`, all three integer squares are1. Thus P*Q
is a unit. It cannot be -1: integer factors of -1 are1 and-1 in either
order, which the two exclusions forbid. Hence P*Q=1; P is an integer unit,
and P != -1 forces P=1. The correction A*(P-1) vanishes. The same argument
applied first to the old sphere also gives P=1 before removing or inserting
the correction. Therefore each new sphere has exactly the old sphere's
positive solutions. The maps in both directions retain all thirteen
coordinates, with no new witness or stronger hypothesis.

`ThirteenFirstNormCorrection92.correction_zero_iff` is the frozen arbitrary
integer coefficient theorem. The new Lean leaf instantiates it for A90 and
A88, proves the evaluation and ring-map identities, and composes the actual
current four-port no-positive-zero endpoint with the real
`DiophantineConsistency.ConZFC`. This is an external Lean equivalence; it
is not an internal proof in HA, PA, or ZFC. The internal HA task remains
open at its separately documented boundaries.

The polynomials differ from their parent. In general their exact difference
is `A^2*(P-1)^2-2*U*A*(P-1)`. The auditor proves this complete formula and
records distinct actual-port outputs at a positive assignment; it does not
mistake zero-set equality for polynomial identity.

## Fully paid operations

Both graphs retain the entire parent75 prefix, substitute the corrected
auxiliary into its existing square, and insert only the following rows.
All binary multiplications, including multiplication by2 and16, are paid.
The original75 rows have42 multiplications,18 additions,15 subtractions.

For degree90 the17 extra operations are

```
bG=b*G; bGT=bG*T; WG=bGT*V; WGh=WG*h; VC=V*C;
bGf2=bG*f2; bGf2R=bGf2*R; gap2=VC-bGf2R;
f2T=f2*T; term2=f2T*gap2; twoterm2=2*term2;
bracket=WGh+twoterm2; coeff0=WG*bracket; coeff=16*coeff0;
Pminus1=P-1; correction=coeff*Pminus1; correctedU=U-correction.
```

The total is92: 55 multiplications,19 additions,18 subtractions.
For degree88 the22 extra operations are

```
bG=b*G; bG2=bG*bG; Vh=V*h; firstterm=bG2*Vh;
VC=V*C; XC=X*C; twoBG=2*bG; gap3=twoBG-XC;
VCgap=VC*gap3; f2R=f2*R; bG2f2R=bG2*f2R;
inner3=VCgap-bG2f2R; f2inner3=f2*inner3; twoinner3=2*f2inner3;
bracket=firstterm+twoinner3; T2=T*T; T2V=T2*V;
coeff0=T2V*bracket; coeff=16*coeff0;
Pminus1=P-1; correction=coeff*Pminus1; correctedU=U-correction.
```

The total is97: 59 multiplications,19 additions,19 subtractions.
Every row, all thirteen unknowns, and all four ports are reachable from each
output. Exact unequal modular evaluations with the actual ports also prove
polynomial dependence on each leaf; reachability alone would not prove it.
The graphs materialize only92/90 and97/88, not the dominated99/88 or100/88
schedules. A proposed91/90 hand count was rejected because it omitted one
binary multiplication; its separate exploratory receipt is preserved.

## Exact degrees after actual coefficient specialization

At every gate the auditor computes a sharp upper bound and its complete
highest homogeneous component in the thirteen unknowns, keeping the ports
symbolic with degree0. The main norm Q is expanded completely (323 terms),
proving degree18 despite its initial cancellation. Through the correction
it retains the highest seven homogeneous layers (drops0 through6). A
product term omitted by this cutoff cannot reach any retained degree under
the established degree bounds. Addition is truncated at the corresponding
new bound. The only sharpenings are independently expanded Q and the final
corrected auxiliary, where all higher retained layers cancel exactly.
After finding that auxiliary's nonzero leader only its exact leader is
needed for its square and the final sum.

For U90 the layers48,47,46 vanish and degree45 is nonzero. With
`B=beta*J`, `k0=eta+zeta`, `C0=B-F-alpha`, its complete75-term leader is

```
32*B^20*k0^4*f^6*T^4*s^6*w^2*C0*((w-B*K0)*C0+B*F).
```

Its square is the complete639-term degree90 leader. For U88 the layers
48,47,46,45 vanish; its complete302-term leader has degree44, and its square
is the complete7,112-term degree88 leader. The full leaders, every gate's
degree/leader, and all cancellation records are in the deterministic
certificate. No assertion that the whole high-degree polynomial is fully
expanded is needed or made. The other branches have degrees80 and72.

The selected degree90 unknown monomial has exponents
`J40 alpha4 f12 T8 s12 w6 zeta8` and coefficient1024*beta^40.
The selected degree88 monomial has exponents
`J38 alpha4 f12 T8 s10 w8 eta2 zeta6` and coefficient1024*beta^38.
The auditor checks that no other symbolic-port monomial contributes to each
selected unknown monomial. Both coefficients are strictly positive at the
actual beta, proving the exact degrees after specialization.

## Verification scope

The deterministic stdlib-only auditor pins the accepted parent graph,
ordinary proof, Lean sources, and current native coefficient receipt. It
reconstructs the four complete current integers from all3297 native
coefficients, checks every raw/gzip byte, pins MF shifted once, and validates
all scalar boxes. It compares every unchanged parent row and unaffected
gate leader, binds both entire new formulas, rejects arithmetic and
structural corruptions, and checks actual-port dependence and nonidentity.
Default and `-O` executions are read-only; only `--write` materializes this
new packet. No incoming or project Python module is imported or executed.

These are additional operation/degree tradeoffs with the same13 positive
unknowns and complete coefficient tuple. They preserve accepted parents
and do not assert global size minimality, a newly formalized calibration,
an internal HA endpoint, or a change to the maintained display.
