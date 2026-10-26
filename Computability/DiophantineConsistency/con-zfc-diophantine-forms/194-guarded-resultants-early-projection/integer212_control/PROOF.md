# A scaled dyadic Pell pair: 212 unrestricted integer coordinates

## Result and boundary

The literal equation `integer212/equation.json` is the sum of the squares of
151 quadratic residuals in 212 independently unrestricted integer variables.
Its collected quartic has 5,357 nonzero terms and height 17,592,186,044,420.
The maximum residual coefficient is 4,194,304. The accompanying coefficient
file lists every term. The construction has an integer zero exactly when
there is a finite refutation in the fixed effective ZFC presentation.
Consequently ZFC proves its nonsolvability equivalent to Con(ZFC); this
statement does not assert either nonsolvability or consistency.

The immediate literal parent is source173's pre-optimization affine213
system, at ProveIt commit ecb9a4b4dda617512952525d50f17343700aac52. Its complete
unchanged original release is retained in `inherited/Source173.zip`, including
its ordinary proofs, source-to-equation projections and independent verifier.
The parent has 213 variables, 152 rows and, after its optional optimization,
5,402 quartic terms with height 2,417,851,639,242,452,488,945,685. Thus this
construction saves one coordinate, one row and 45 terms while lowering that
height by more than eleven decimal orders. The round22 215-variable equation
has much smaller coefficients and remains a useful incomparable alternative.
No global minimum or new proof-assistant compilation is claimed.

The source173 anchor replacement, constructor-depth bound, factorial-free
compiler, Horn-flow argument and six exact projections are credited, not new.
The fourfold weak-frame pooling estimate comes from round22; its proof is
retained in `credited/ROUND22_AFFINE_WEAK_FRAME.md`. The new combination is a
scaled growth Pell pair, a weakened but sufficient cap on that pair, and a
nondegenerate affine growth base. Their unbounded proofs follow here. Finite
checks certify every literal algebraic change, not these unbounded theorems.
The inherited logical endpoints are `KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`, not a machine execution
or a specialization of Jones' universal polynomial. The source closure is
an ordinary-proof closure, not a complete compilable Lean dependency tree.

## 1. Changed semantic quantities and literal coordinates

Put D=2^20=1048576. Keep the old coordinate t unrestricted, discard the
private coordinate that enforced t=16+4h^2, and use

    d=4t+2,          K=D t,          F=d^K.                 (1)

The last notation is a theorem about a quadratic power certificate, not an
exponentiation operation in the literal equation. In particular no sign of
t or F is assumed here. The integer d is always even, nonzero and nonunit.

Keep the thirteen principal Pell pairs with nominal indices

    t, F+t, a,b,c,d_local,S,y+1,S',u,x,vq,C.

Here d_local is a local representative, distinct from growth base d. The
reused anchor is the existing pair at C, and C is stored as twice an integer.
Replace the fourteenth, growth pair by three coordinates w,z,Z representing

    X=1+D w,       Y=D z,       Z=A z.

Its two literal equations are

    Z-Az=0,       2w+D(w^2+z^2-Z^2)=0.                    (2)

Multiplying the second equation by D gives exactly
X^2-(A^2-1)Y^2-1=0, modulo the first. Thus there is no discarded divisibility
condition or hidden extra variable. With T=d^2-2Ad+1, its power row is

    F-1-Dw+DZ-dDz+T q_growth=0.                          (3)

The sign of T is the opposite of the positive-form modulus 2Ad-d^2-1 used
below; divisibility is the same. All terms in (2)-(3) are at most quadratic.

In the pooled orientation replace ONLY the growth-pair contribution

    (X-1)^2+(Y-Dt)^2    by    w^2+(z-t)^2.              (4)

The literal parent orientation has already had fourteen norm rows subtracted.
The producer removes its exact old growth contribution
2-2d_old-2Z_old+Z_old^2+D^2t^2-2DtY_old, inserts the new expression in (4),
and later replays explicit integral row operations. The checker reconstructs
the raw orientation from all actual shifted pairs before comparing this edit.

The anchor cap now uses z^2, not Y^2=D^2z^2, for this one pair:

    Y_C^2=C^2+1+sum_(other 12 nonanchor pairs) Y_i^2
                 +z^2+r^2+s^2+v(v+1).                 (5)

This is a semantic weakening, justified in Section 3; it is not an asserted
pointwise equivalence of arbitrary old witness tuples. The literal cap row
is unchanged because its former ordinate coordinate now stores z.

## 2. Weighted weak frame, parity and quantitative growth

All 35 actual source atoms (including duplicates) and all 48 base/index/output
ports of the sixteen requests are explicitly listed in the certificate.
They include d=4t+2, K=Dt, C=2c0, F+t, q,q+1, BH, and every power output.
They are affine forms L=c+sum a_j u_j in arithmetic coordinates only. Define
w_j as the largest |a_j| among these forms and set

    W=22+sum_j w_j u_j^2.                              (6)

In this ledger w_t=D, w_c0=2, and every other weight is 1; |c|<=2.
For every integer u, |u|<=u^2. Therefore each |L| is at most
2+sum_j w_j u_j^2<W. This is an absolute bound, NOT the false assertion L^2<W.
The complete atom and coordinate census is checked independently.

Use the same fourfold Pell frame as round22:

    U=4W(2v_frame-1),    V=(4W+1)U,    A^2+U^2-V^2=1.   (7)

These are three quadratic rows using the existing coordinates. Since U,V
are even, A is odd. No sign of A is assumed. Classification of the Pell
solution (|A|,|U|) at center 4W+1, together with U a nonzero multiple of 4W,
gives an absolute index at least 4W. Consequently

    |A|>(4W)^(4W),   |A-1|>4W^3,   |A|>D+1.            (8)

The last inequality already holds at W=22: 88^4>D+1, a fortiori 88^88>D+1.
For completeness choose the frame index 4W. The familiar congruence
Y_(4W)(4W+1)=4W modulo 8W ensures that U/(4W) is odd, supplying v_frame.
The frame is chosen only after all finite arithmetic coordinates and W.

## 3. Scaled cap and dyadic classification, before arithmetic signs

The private anchor norm, squared-divisibility and comparison rows are
unchanged. Equation (5) gives |Y_C|>|C| and Y_C!=0. The source173 signed
anchor proof therefore applies verbatim: classify its absolute index i>0;
the auxiliary comparison gives i=+/-C modulo 2|Y_C|; since
1<=i<=|Y_C| and |C|<|Y_C|, C!=0 and i=|C|. This uses no sign or interpreted
arithmetic meaning of C. In particular the possibly degenerate anchor index
zero is excluded before any comparison requiring a nontrivial pair.

Every unchanged pair has absolute index <|C| by (5). For the scaled pair,
(5) gives |z|<|Y_C| and hence |Y|<D|Y_C|. If its absolute classified index
were at least |C|+1, Pell recurrence at a=|A| would give

    |Y|>=Y_(|C|+1)(a)>a Y_|C|(a)>D|Y_C|,

contradicting the preceding bound. Thus its absolute index is <=|C|<W.
Equality here is allowed; strictness is unnecessary for orientation.

For odd a, every Pell abscissa X_n(a) is odd. Reduction modulo 2 gives
Y_n(a)=n modulo 2. Repeated doubling Y_(2n)=2X_nY_n therefore proves, for
nonzero n,

    v2(Y_n(a))=v2(n).                                 (9)

Since D divides the scaled ordinate, the classified index is D*l for some
integer l. The zero ordinate has index zero and is included separately.
For D>=4, X_(D*l)(a)=1 modulo D: use
X_(2n)-1=2(a^2-1)Y_n^2 and D/2 divides Y_(D*l/2).
Our physical abscissa is 1 modulo D. It cannot be the negative of this
canonical abscissa, since +1 and -1 are distinct modulo D. At zero index,
X=-1 is excluded for the same reason.

These conclusions also handle A<0. The index D*l is even;
X_(D*l)(A)=X_(D*l)(|A|), and the ordinate sign chooses signed l because
Y_(D*l)(A) changes sign with the sign of l. Thus the physical pair is the
canonical signed pair at the actual signed parameter A.

Crucially we NEVER cancel D modulo the even integer A-1. Instead the exact
integer polynomial identities from repeated doubling give

 Y_(D*l)(A)/D=Y_l(A) product_(j=0,...,19) X_(2^j*l)(A),
 (X_(D*l)(A)-1)/D
   = (D/2)(A^2-1)(Y_(D*l/2)(A)/(D/2))^2.

The second identity is also valid at l=0. Evaluating these polynomials at
A=1 proves the genuine congruences

    z=l mod(A-1),        w=0 mod(A-1).                 (10)

They are valid at negative A and signed l as well.

The old orientation reductions for the other thirteen pairs have abscissa
residues +/-1 and signed ordinate residues of absolute value <W. For the
new pair (10) gives residues 0 and l, with |l|<W. All fourteen ordinate
errors have absolute value <2W; all abscissa errors have absolute value at
most 2. The modified orientation thus has a nonnegative small residue E with

    0<=E<56W^2+56<4W^3<|A-1|       (W>=22).

Divisibility by A-1 forces E=0. Every other pair is canonically oriented at
its nominal index. The new error gives l=t, so the scaled pair has physical
index Dt. Neither positivity of t nor any arithmetic power was used.

## 4. Power interpretation under the weak frame

For a pooled block of r<=15 requests at nonzero integer base n, let its
canonical pairs have indices k_i, outputs m_i, and Z_i=A Y_i. The retained
quadratic rows are

 K_n-2H-(2A-n)L_n=0,   S-nK_n+L_n=0,
 H=sum Y_i(m_i-X_i),   S=sum((m_i-X_i+Z_i)^2-Y_i^2).

They imply that T_n=2An-n^2-1 divides sum(m_i-X_i+Z_i-nY_i)^2.
Since T_n=-1 modulo n, n is invertible modulo T_n. Put b=W-1. Canonical
signed-index Pell congruences, multiplied by n^(2b), give divisibility of

    E=sum_i (m_i n^b-n^(b+k_i))^2.

Every exponent is nonnegative and |n|,|m_i|,|k_i|<=b. For |n|>=2 each
summand is <=4b^(4b); the same loose bound covers n=+/-1. Hence

    0<=E<=60b^(4b)<(4W)^(4W)<|T_n|.

The last inequality follows from
|T_n|>=2|A|-(W-1)^2-1>|A| and (8). Thus E=0. At a nonunit base this
forces k_i>=0 and m_i=n^k_i. At a unit base it proves the signed unit power
without claiming a nonnegative index. The singleton requests have the same
conclusion, either directly or by squaring their divisibility error (r=1).
The scaled pair in (3) is just its physical canonical pair, so it is covered.
Conversely genuine powers give the two pooled quotient witnesses by the
identity S-2nH=T_n L_n and K_n=2H+(2A-n)L_n. This is an integral fresh
witness construction, not an inverse on arbitrary preliminary tuples.

## 5. Noncircular horizon and signed arithmetic bootstrap

The growth base d=4t+2 is always even and nonunit. The singleton lemma first
gives Dt>=0, hence t>=0, and F=d^(Dt). If t=0, then F=1 and
 y=F(2v+1) is odd. The endpoint equations reduce to

    x=2+(y+1)u0,      x=1+(y+1)ut,

which would make the even integer y+1 divide 1. This excludes t=0, including
y=-1. Therefore t>=1, d>=6 and F>=6^D>2^32; F is positive and even.

Now follow the source173 sign recovery in its proper order. The raw row
B*eta=C+F+1 has odd right side, because C is even. Thus B!=0. The raw radix
multiplier H=2+4(C+a+b+c+d_local+S+S'+u+vq) is 2 modulo 4, regardless of
representative signs, so |BH|>=2. Its singleton gives x>=0 and q=(BH)^x.
If x=0, the last endpoint would make 1+(t+1)y divide -1, impossible for
t>=1 and |y|>=F. Hence x>=1 and |q|>=2.

Interpret the q pool next. Its y+1 index is nonnegative. Since y is a nonzero
multiple of positive F, this gives y>=F. The first endpoint forces u0>=0,
and the last forces ut>=1. In particular

    x>=F+1,        x>=2+(t+1)y.                        (11)

Now |q|>=2^x and x>3, so |q+1|>=2. Only now interpret the q+1 pool. All
nine actual representatives and their numerator powers are nonnegative;
H>=2. Normalized signed-remainder recovery authenticates
B=binom(F+t,t)>0. Therefore q>0 and N=B^x>0, as in the parent. No earlier
step assumes these last signs.

The source173 remainder argument still applies: its first-digit coefficient
bound (F+t)^t<=2^(t(F-1)) and |q|>=2^((t+1)F+2) hold for all the present
values. The common remainder norm, all ten digit rows, and all retained
strict local ranges are unchanged. The corner case y=F is excluded after
local recovery by the parent's positive-accumulator argument, not prematurely.

## 6. Small horizons, local label bounds and soundness

Two old thresholds are explicitly replaced rather than silently reused.
First, Lambda_t<=4^(t-1), while F>=6^(D t)>16^t for every t>=1. Thus the
all-primes binomial selector applies with radius R=F, including t=1.
Second put R0=2+t+x+y+F. Since F>=t, y>=F and x>=2+2y, R0<3x. If
2^s<=x<2^(s+1), then s>=32 and

    2^23 log2(3x)<2^23(s+3)<2^s<=x.

The strict middle inequality holds at s=32 and persists by induction.
Consequently the inherited literal local-degree bound is
L_local<R0^(2^23)<2^x<=p^(e x), supplying exact local recovery.

For the deleted derived-label range, use the pinned source173 depth-19
constructor ledger with comparison base d=4t+2. At t>=2 we have d>=10,
so its estimate that each constructor on arguments below s is <8s^2
gives, by the usual exponent recurrence, every label <d^(D-1). The
smallest horizon t=1 requires a separate argument, not a silent reuse of
the hypothesis d>=8: all local parameter leaves are zero, all constant
leaves are at most one, and we start with s0=2. Iterating sr+1=8sr^2
gives sr=16^(2^r)/8. For every r>=0 this is less than
6^(2^(r+1)-1), since 16<36 and 1/8<1/6. At depth r<=19 the label
is therefore <6^(D-1)=d^(D-1) as well. In all cases choose L=d^D. Then

    L>=t,      F=d^(Dt)=L^t.

The source173 sharp product-separation lemma therefore applies even at the
smallest horizon. For clarity: unequal factor counts contradict F+1>L^t;
for equal counts m<=t, each positive elementary symmetric coefficient lies
in [1,L^m] subset [1,F], so differences have magnitude <F. The least nonzero
coefficient cannot vanish when evaluated at F. Unique factorization recovers
label multisets. Zero labels contribute units and are omitted.

The unchanged local-row, boundary, range and positive-accumulator arguments
now produce a balanced finite single-conclusion Horn flow. The source173
Horn closure proof extracts a refutation even in the presence of cycles.
Its literal C222 calibration then yields a finite ZF refutation and, by the
retained constructible-choice equivalence, a finite ZFC refutation. This
completes soundness without circular arithmetic positivity.

## 7. Completeness and its order of choices

Start with a finite C222 refutation, all its local parameters and padding.
Choose an integer t>=1 sufficiently large to exceed those finite parameters
and its length. Set d=4t+2, K=Dt, F=d^K. Since v2(d)=1,

    v2(F)=Dt>v2(t!),   v2(F+i)=v2(i) (1<=i<=t).

The inherited beta CRT construction gives arbitrarily large positive
 y=F a^2 with a odd and divisible by the odd part of t!. It satisfies the
retained odd-linear equation with v=(a^2-1)/2, and can dominate all required
finite accumulators. Choose an arbitrarily large positive beta code x in its
CRT class before defining N=B^x or choosing the independent representatives.
All beta moduli are odd. The binomial
B=binom(F+t,t) is odd by the displayed valuations, so N^2 is odd.

Choose the eight ordinary CRT representatives in their required residue
classes. Choose the remaining representative C even and cofinally large in
its own class modulo N^2, exceeding every other nominal index including Dt.
This is possible because N^2 is odd. Only then define H and q=(BH)^x and
all associated true powers. The actual frame (6) is computed after these
arithmetic choices. No earlier modulus depends on the enlarged C or q.

Choose the positive canonical fourfold frame A and every ordinary principal
pair. For the growth pair define

    z=Y_(Dt)(A)/D,  w=(X_(Dt)(A)-1)/D,  Z=A z.

The doubling identities above make these integers and make w and z-t
multiples of A-1. Equations (2)-(4), including the orientation quotient,
therefore have integral witnesses. Because C>Dt and C exceeds the other
indices, the parent cap slack remains nonnegative even with the smaller
scaled term z^2. Its universal ternary representation supplies the guard
r^2+s^2+v(v+1). Every private comparison witness is supplied by the same
source173 construction: C even gives odd abscissa and even ordinate; take
comparison index C Y_C, use its odd squared quotient, and choose the
comparison center by CRT. This does not require the old horizon equation.
Finally true powers supply all singleton and pooled quotients and all
unchanged local/Horn wires. Apply the recorded integral coordinate changes
and delete the unused horizon-root slot. This yields a literal zero.

## 8. Exact algebraic maps and reproducibility

The semantic step has the stated scope of fresh zero-existence constructions,
not an old-tuple bijection. Its physical pair map is exactly

 old_d=1+D(w-Z),     old_Y=D z,     old_Z=D Z.

The weakened cap and discarded old horizon prohibit claiming that this map
alone lifts every new tuple to every old equation. `base213/equation.json` is an explicitly marked staging array: row130 and
coordinate184 are inactive placeholders, not an additional horizon condition.
After the semantic step, every optional optimization is genuinely bijective: each coordinate image
is x_i -> x_i+L(other coordinates), inverted by negating L; each row operation
R_i -> R_i+k R_j is inverted by -k, in reverse order. The private old root
and its row are then omitted, and all remaining indices are renumbered.
`coordinate_map.json` gives every exact image and retained coordinate/row.
`semantic_certificate.json` lists every changed literal coefficient, physical
pair map, actual atom and weight. No active certificate contains an absolute
workspace path. Historical path strings inside the unchanged source archive
are provenance only and are never used to locate new inputs.

`check.py` independently reconstructs the source identities, complete edited
system, every forward/inverse optimization, every collected quartic term,
all metrics and readable residuals. `verify.py` runs it normally or with
Python -O, copies the whole package to a fresh temporary location, rebuilds
there, and compares every generated JSON byte. The optional `--parent` also
runs the retained source173 verifier. None of these finite checks decides
consistency, searches for a zero, or substitutes for the ordinary proof.
