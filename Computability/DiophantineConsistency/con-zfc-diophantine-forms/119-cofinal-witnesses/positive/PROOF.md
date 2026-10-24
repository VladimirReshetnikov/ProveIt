# Reusing the auxiliary coordinate after coprime Pell fusion

Date: 24 October 2026. Repository snapshot:
`45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6`.

The new step combines two constructions present in the incoming archives:
coprime first/strong Pell fusion and the auxiliary fifth-index gap. It
removes the transport majorant and, in the cheapest pair, the product
center. It is an ordinary proof formalizable in ZFC, composed with the
identified native/controller/refutation calibration. It is not a new
end-to-end Lean proof or a global minimality theorem.

| Equation | Positive unknowns | Binary operations | Exact degree |
|---|---:|---:|---:|
| uncentered | 10 | 89 | 288 |
| upper | 10 | 91 | 283 |
| sharp | 10 | 92 | 278 |
| direct_uncentered | 10 | 94 | 262 |
| direct_upper | 10 | 96 | 258 |
| direct_sharp | 10 | 97 | 254 |

The earlier saturated equations cost 92/283, 93/278, 98/258 and 99/254.
The four centered rows above lower cost at the same exact degrees. The
89-operation row is a new cost/degree tradeoff. Degrees across different
variable domains or coefficient tuples must not be conflated.

## 1. Complete polynomial definition

Take the ten strictly positive integer unknowns

    J,F,alpha,i,T,w,Y,n,eta,zeta

on the ordinary chart; replace w by x on the direct chart. The four fixed
ports beta,K0,MC,MF are the complete coherent compact44 BFS tuple
reconstructed by `coefficients/recipe_compact44.py`. Their compressed
integer payloads and immutable byte hashes are included. No port is an
unknown. No port from the original44 tuple is substituted into this tuple.

In both charts put

    q=beta J+1, mu=q²+1, k=eta+zeta, c=kY+eta,
    X=wq                           [ordinary],
    X=q+x                          [direct],
    A=mu Y(X+1)+1, H=4A-5, Delta=A²-1,
    V0=X(mu Y)², E=V0(V0+1)k²+1,
    R=[(q-1)(q-F)+alpha](q²-1)+(MC+q MF)J,
    e=k-R-1, C=q-F-alpha,
    U=i c², Df=1+Delta U² E, Q=Delta² U² E, delta=Q-1,
    b=c(T+alpha)-R, V=Df b-c, Dnum=Q V²-1,
    Kpos=X(3c-2X)+2.

For the ordinary chart put

    B=(K0+w)C-F, h=q-1, P=q³(q-1), Dlow=0.

For the direct chart put

    B=(q K0+X)C-qF, h=q(q-1), P=q⁴(q-1), Dlow=(q-1)X.

Choose the polynomial center

    Cg=0                           [uncentered],
    Cg=(A+1)U E                    [upper],
    Cg=A U E                       [sharp].

Every new equation uses L=b, not the older k(T+alpha). Define

    M=P mu² H,
    Z=P mu²[H(n+V+Cg-bB)+Kpos]
      +H[mu²(hY-q³B-Dlow)-P e],
    s=delta Z², u=delta M² E Df, v=M² Dnum,
    N=(s-u-v)²-4uv.

The requested equation is simply N=0. These are polynomial
abbreviations: there are no radicals, divisions, variable exponents,
extra witnesses, or predicates in the exported polynomial.

For explanation only, put W=1+hb. The exact rational carrier reads

    Z/M=n+V+Cg+Kpos/H+Y/q³-WB/h-e/mu²-d,

where d=0 ordinarily and d=X/q⁴ directly. The identity uses P=q³h.

## 2. Root recovery and the inherited early interface

The changes affect only the rational center, which had no sign premise
in the parent's recovery proof. For completeness, its key argument is
as follows. Let G=E Df and Ystar=Dnum/delta. For every positive assignment,
G,Ystar,delta,M are positive. To see positivity of Ystar, either b=0
and V=-c, or |V|>=Df-c>1; hence QV²-1>0.

The equation divided by delta² M⁴ says

    [(Z/M)²-G-Ystar]²=4G Ystar.

The two radicands cannot coincide: Q and G are divisible by E>1, while
Dnum=Q V²-1 is -1 modulo E. Thus Z/M cannot be zero. A nonzero rational
signed sum of two positive square roots makes both roots rational,
by solving for one after squaring. Since G is an integer, it is a
square. Since Df=1 modulo E, gcd(E,Df)=1, so

    E=tau², Df=f², tau,f positive integers.

The adjacent-Pell rational-root descent makes sqrt(Ystar)=y a positive
integer. Its complete proof is reproduced in
`provenance/saturation_semantics.tex`; no parity or transport conclusion
precedes that descent. Set the proof-only integer I=U tau. Then

    c² | I, f²-Delta I²=1, Q=(Delta I)²,
    QV²-(Q-1)y²=1,
    Z/M=epsilon_g tau f+epsilon_y y.

Write g=tau f. The literal U is not confused with the recovered I.
The strong/auxiliary folding theorem applies uniformly to these data and
gives c=psi_A(p) for a positive odd p. First-Pell classification gives

    k=2 psi_(2V0+1)(n0), n0>=1.

The case n0=1 would give k=2, eta=zeta=1 and c=2Y+1 strictly between
psi_A(1)=1 and psi_A(2)=2A. Hence n0>=2, and

    k>=8V0+4, c>kY>=k>8q^5, c>2X, Kpos>0, H>3X.

These implications use neither B>=0, parity of q, nor the later identity
p=R. They are the same uniform early interface as in the saturated
parent, with the same complete port tuple.

## 3. The auxiliary coordinate pays for the fused root

The native mask port bounds give R<q^4+(alpha+2)q². Since q>=32,
alpha>=1 and c>8q^5, this is strictly smaller than c alpha/4:

    2q^5 alpha-q^4-(alpha+2)q²
      >=2q^5-q^4-3q²>0.

Consequently b=c(T+alpha)-R>c(T+3alpha/4)>c. In particular V>0.
Since c>=3, the odd index p is at least 3, and

    c>=psi_A(3)=4A²-1=4Delta+3.

Put S=Delta I, so Q=S². The auxiliary equation is

    (S V)²-(S²-1)y²=1.

Pell classification gives S V=chi_S(v) for a positive index v. The
recurrence modulo S shows that v must be odd. Since b>c,

    V=Df b-c>(Df-1)c=Delta I² c>4Q.

The cases v=1,3 have V=1 and V=4Q-3, respectively; both are excluded.
Therefore v>=5 and

    V>=16Q²-20Q+5>8Q².

Here Q>=3. Also Df<Q and hence

    b=(V+c)/Df>8Q.                         (1)

This fifth-index argument is unbounded and occurs before the transport
sign conclusion. The extra saturation divisor tau in I does not weaken
any hypothesis: all statements above use only the recovered integer I,
c²|I and the unchanged strong/auxiliary identities.

The strong norm gives f<AI, and hence

    g=tau f<A U E<Q,

because Q/(A U E)=Delta² U/A>1. Also Q>X. Thus

    g+d<2Q<b/4                            (2)

in either chart. In the ordinary chart this is deliberately stronger
than needed.

The remaining positive remainders are smaller than b/4 each. Indeed
Q-1>2Df, because Q-1-2Df=Delta(Delta-2)I²-3>0. Thus

    0<y-V=(V²-1)/[(Q-1)(y+V)]
             <V/[2(Q-1)]<Df b/[2(Q-1)]<b/4.

Finally b-e=c(T+alpha)-k+1>0. Even when e is negative, the upper bound

    e/mu²<b/mu²<b/4                       (3)

is valid. An absolute-value bound or integrality of e/mu² is unnecessary.

## 4. Soundness of all six equations

Solve the signed carrier for n:

    n=epsilon_g g-Cg+(epsilon_y y-V)
       -Kpos/H-Y/q³+WB/h+e/mu²+d.

For the uncentered equation, (2), (3), and y-V<b/4 imply that every
positive term other than WB/h has total less than 3b/4. If B<=-1,
then W=1+hb and h>0 give WB/h<=-b-1/h<-b. It follows that n<0,
contradicting positivity. Hence B>=0 in both charts.

The two centered equations have Cg>0, so exactly the same argument
already proves their soundness. Alternatively, the parent's sharper
inequalities g-Cg+d<0 give n<b/2-b<0 without using (1). This latter
proof explains why simply removing L=k(T+alpha) is valid in the centered
parents as well. Either proof is acyclic.

The literal definition of B now forces C>0. The inherited mask argument
gives 3q<R<q^4-2. The strong-rank and signed-index lemmas recover p=R;
odd R then gives even q and odd J. Only now is the denominator unit
argument licensed, yielding mu²|e. The first-index lemma recovers
n0=(R+1)/2. The ratio and whole-product projection recover X=2^R.

Every changed center Cg is an integer, and W=1 modulo h, so none of
the inherited denominator, index, projection or source interfaces is
altered. In the direct chart q|X is derived only after the main projection;
then q^4|X and B=q Bt with Bt=(K0+X/q)C-F. The residual fractions give
q³|Y and (q-1)|Bt. Fixed-minus parity gives R=3 modulo 4, and the
half-binomial rounding identifies Y. A fresh unscaled source witness
at A_source=Y(X+1)+2 is reconstructed; the scaled I is not divided or
reused as that source witness. The whole native/controller calibration
then produces a finite syntactic ZFC refutation.

The detailed inherited index and projection proofs are included in
`provenance/saturation_source/proofs/`; the saturation application is
included verbatim in `provenance/saturation_semantics.tex`. The new
equations preserve every hypothesis used there.

## 5. Positive completeness

A finite refutation gives the parent's canonical outer data with
X=2^R, R=3 modulo 4, R>3q, c=psi_A(R), E=tau², and integers

    t=Bt/(q-1)>=0, rho=e/mu²>=0, sY=Y/q³>0,
    kappa=Kpos/H>0.

Choose the strong pair anew. The determinant-one Pell matrix
[[A,Delta],[1,A]] has a finite positive order modulo c² tau. A
positive multiple m of this order gives I=psi_A(m) divisible by
c² tau. Put i=I/(c² tau)>0 and f=chi_A(m). Then the literal
Df=f² and Q=(Delta I)² hold exactly. This is a finite-period
construction, not an assumption that a former strong witness already
has the new divisor.

The inherited universal auxiliary-completeness lemma supplies the
canonical witness Vstar=chi_(Delta I)(R)/(Delta I), y=psi_(Delta I)(R),
and a positive Tstar with Vstar=f²(cTstar-R)-c. Its explicit growth
gives Tstar>alpha, so T=Tstar-alpha>0. Moreover, writing u=y-Vstar,

    u>(9/4)Delta² I²>4I²,
    kappa<c<I, sY<Y<c<I, UE=I tau<I².

These statements, including Tstar>alpha, are proved in the included
saturation semantics; they do not depend on the transport majorant.
Use the newly prescribed W=1+hb. Ordinarily choose

    n=g-Cg+u-kappa-sY+Wt+rho.

For the uncentered case, g>2c>kappa+sY and all other summands are
nonnegative, with u>0; hence n>0. For either centered case,
0<Cg-g<2UE, so the total negative loss is less than 2I²+2I<4I²,
while u>4I². Again n>0. The normalized carrier is g+y, so the norm
vanishes. The proof uses a fresh positive existence witness, not a
purported positive inverse for arbitrary old n.

For the direct chart keep all kernels and put x=X-q>0. Since q^4|X,
define n_direct=n_ordinary+(W_direct-W_ordinary)t+X/q^4>0. The centers
and kernels agree; M_direct=q M_ordinary and Z_direct=q Z_ordinary.
Thus N_direct=q^4 N_ordinary=0. This proves both directions for all
six complete equations.

## 6. Exact global degrees

The argument is in the formal Laurent-series field under uniform
witness scaling t, with all four coefficient ports fixed. This proves
ordinary total degree; no analytic convergence is used. Let q0=beta J,
k0=eta+zeta, and x0=q0+x. For the new carrier

    Z/M=V+Cg+mathcalE,

the rational remainder mathcalE has degree at most 6: the only raised
term is -bB, and deg b=4, deg B=2. The previous bound was 4.
All relevant leading radical defects have degree at least 17, so
this change cannot alter any centered leading form.

Choose formal roots g²=E Df near AUE and y²=Dnum/delta near V.
The degree table is

| chart | A | U | E | Df | delta | V | M | g | C_upper-g | C_sharp-g |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| X=wq | 5 | 5 | 18 | 38 | 48 | 42 | 13 | 28 | 23 | 18 |
| X=q+x | 4 | 5 | 16 | 34 | 42 | 38 | 13 | 25 | 21 | 17 |

The identities (AUE)²-E Df=U²E²-E and
(y-V)(y+V)=(V²-1)/delta give the listed defect degrees; y-V has degree
-6 and -4 respectively. The exact norm identity is

    N=delta² M⁴ product_(sigma,rho=+-1)(Z/M+sigma y+rho g).

In the uncentered case the two sigma=+1 factors have leading form 2v0;
the other two have leading forms g0 and -g0, because mathcalE has
degree at most 6. Hence the leading form is

    -4 delta0² M0⁴ v0² g0².

It follows that the ordinary degree is
2*48+4*13+2*42+2*28=288 and the direct degree is
2*42+4*13+2*38+2*25=262. The exact homogeneous forms are

    ordinary uncentered:
      -2^10 q0^152 w^30 Y^62 i^10 k0^32 (q0-F)²;
    direct uncentered:
      -2^10 q0^126 x0^30 Y^62 i^10 k0^32 (q0-F)².

The centered leading forms are unchanged from the parent:

    ordinary upper:  2^11 q0^149 w^29 Y^61 i^10 k0^32 (q0-F)²;
    ordinary sharp:  2^10 q0^146 w^28 Y^60 i^10 k0^32 (q0-F)²;
    direct upper:    2^11 q0^124 x0^29 Y^61 i^10 k0^32 (q0-F)²;
    direct sharp:    2^10 q0^122 x0^28 Y^60 i^10 k0^32 (q0-F)².

Each is nonzero for every fixed beta>0, proving degree attainment for
the actual enormous coefficient tuple. The Laurent-series upper-bound
argument and nonzero forms are the proof; exact specialized polynomial
replays in verify.py are independent finite checks of transcription.

## 7. Finite specification and scope

The six JSONs contain every live arithmetic gate. A binary addition,
subtraction, multiplication, square, or fixed scalar multiplication costs
one gate. Aliases cost zero, and no coefficient is counted as an unknown.
The builder makes only the declared row deletions/rewrites; the independent
checker compares every actual row with its frozen parent, reconstructs
all fixed coefficients, checks complete liveness, expands the universal
norm identity, verifies independent direct formulas at exact signed
integer inputs, and replays exact polynomial degrees over Z. It also
checks the carrier replacement identity in a free polynomial ring.
Checks remain active under Python -O.

Negating the proved finite-refutation/positive-zero equivalence gives

    ZFC proves: (no positive integer zero of N) iff Con(ZFC).

This statement asserts neither consistency itself nor a new proof-assistant
certificate. The native/controller calibration is inherited, precisely
identified, and retained; this packet's new semantic arguments are
Sections 3--5, and its new exact degrees and censuses are Section 6 and
the supplied complete graphs.
