# Strict-frame pooling with an odd-linear beta multiplier

## Result and attribution boundary

The four released equations are literal sums of squares of their complete
quadratic residual lists. Their variables range independently over Z. In
ordinary ZFC, integer solvability of each equation is equivalent to existence
of a finite syntactic ZFC refutation. Equivalently, its integer nonsolvability
is equivalent to Con(ZFC). Neither side is asserted separately. This is not a
new end-to-end Lean/Rocq compilation or an encoded internal ZFC derivation.

The principal advance is a **new compatible composition and exact instance**,
not new claims to the component lemmas. The immediate arithmetic parent is
`ConZFC_Strict_Horizons_2026-10-25`, retained as the original ZIP. It already
provides t=16+h², F=t^t, radius R=F, strict local bounds, q=4z+1, and the
complete signed Pell/frame/C222/refutation proof. Source158 Pooled Powers
already proves the two-row fixed-base pooling lemma and Pell-difference
shears. Source159 Quadratic Projection234 already provides the common-radical
projection and row-basis mechanisms. Source157 Linear CRT already uses an
odd-linear beta multiplier, in a different radix-bootstrap architecture.
Here those methods are composed with the Strict Horizons frame; the new
signed-mod-four/odd-linear bootstrap is justified explicitly below.

The named inherited syntactic interfaces are
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. The direct numerical
C222 route does not use a K215 machine index or Jones's universal polynomial.

## 1. Exact incoming arithmetic interface

The two pinned parents are Strict Horizons `direct/dense235/equation.json`
and `direct/principal236/equation.json`. Their integer profiles are
235/172/12566/7968 and 236/173/4876/7968 (variables/rows/terms/height).
They have seventeen power requests: three initial requests F=t^t, N=B^x,
and q=(BH)^x; eleven at q+1; and three at q, with indices t,y+1,x.
The eliminated old q^(t+1) request is not silently reinstated.

The retained squared frame, semantic anchor, common Pell center, and pooled
orientation constraints canonically orient both Pell coordinates at each
signed requested index before interpreting any power. Their theorem gives
|A|>W^W. Our changes remove only the old power quotients/modulus, not any
orientation or principal-pair condition. The singleton initial requests are
not pooled.

Every source chart has an explicitly checked identity

    W = 2 + sum_(j=1)^34 atom_j².                         (1)

The atoms include t, F+t, x, y+1, F, B, all nine actual CRT representatives,
N, the actual derived label h, q, q+1, BH, and the fourteen pooled outputs.
Every actual base, output, and index of all seventeen requests is among
these atoms. Thus its square is <W; t>=16 implies W>=258.

In dense235, W-2-sum(atom²) is source row152 + 2 row4 + row169.
In sparse236 it is source row153 + row4. All these rows survive pooling.
The dense chart's h is an affine expression obtained from the pinned
source's certified monic elimination. An independent second audit recovers
that expression directly from `cap.index_residue`. The stored y coordinate
is actual y+1, not actual y. The actual radix is 4z+1; the inherited variable
name `radix.odd_square_root_half` is historical, not its current semantics.

## 2. The credited fixed-base pooling lemma

Let W>=258, |A|>W^W and r<=15. Let n be a nonzero integer, and for each i
assume n²,m_i²,k_i²<W. Let X_i,Y_i be the canonical signed Pell coordinates
at A and signed index k_i, and let Z_i=A Y_i. Put

    T=2An-n²-1,  D_i=m_i-X_i+Z_i,
    H_n=sum_i Y_i(m_i-X_i),
    S_n=sum_i(D_i²-Y_i²).

Introduce only two unrestricted coordinates K_n,L_n and quadratic rows

    K_n - 2H_n - (2A-n)L_n = 0,
    S_n - nK_n + L_n = 0.                                (2)

Since Z_i=A Y_i,

    sum_i(D_i-nY_i)² = S_n-2nH_n-T sum_i Y_i².             (3)

Eliminating K_n in proof notation gives S_n-2nH_n=T L_n. Therefore T divides
the sum of squared Pell power errors. The Pell congruence identifies each
D_i-nY_i modulo T with m_i-n^(k_i). Signed powers are legitimate modulo T
because T=-1 modulo n, so gcd(n,T)=1.

For completeness of the size argument, set b=floor(sqrt(W-1)), so b>=16 and
|n|,|m_i|,|k_i|<=b. Multiplication by n^b clears all negative indices. T divides

    E=sum_i [m_i n^b - n^(b+k_i)]² >= 0.

Each summand is <=4b^(4b); consequently

    E <=4r b^(4b) < W^(2b+1) <= W^W < |T|.

Here 4r<=60<W, b²<W, 2b+1<=b²+1<=W, and
|T|>=2|A||n|-n²-1>=2|A|-W>W^W. Thus E=0. At |n|>=2 this forces k_i>=0
and m_i=n^(k_i), since negative k_i would give m_i n^(-k_i)=1. At n=±1 the
signed unit output is exact, without an assertion that k_i>=0.

Conversely, true integer powers give T|(D_i-nY_i) separately. Identity (3)
makes L_n=(S_n-2nH_n)/T integral; define K_n=2H_n+(2A-n)L_n. Both rows in (2)
then vanish. This proves zero-existence equivalence under the retained frame
and canonical-pair hypotheses. It is not a pointwise inverse map recovering
old arbitrary power quotients from arbitrary preliminary tuples.

In the new charts r=11 at q+1 and r=3 at q. Their shared old modulus coordinate
is T_+=2A(q+1)-(q+1)²-1. The q modulus is already its affine expression

    T_q = T_+ - 2A + 2q + 1.                              (4)

Thus there is only ONE old explicit modulus coordinate, not two. Removing
fourteen old quotients and that coordinate, then adding four pooled
coordinates, saves exactly eleven variables and eleven residuals.
`pool_certificate.json` identifies every old power row, retained AY and norm
row, offset, shared modulus, and replacement. The independent checker
verifies (3) as a complete polynomial identity modulo the listed AY rows.

## 3. Odd-linear beta and the noncircular bootstrap

The parent's beta certificate is

    v_beta=(2w+1)²,  y=F v_beta.

Replace it by v_beta=2w+1, then eliminate v_beta monically, obtaining

    y=F(2w+1).                                            (5)

The multiplier can initially be negative. Positivity MUST NOT be assumed.
In literal coordinates this product row is stored_y-1-F(2w+1)=0.

The retained singleton request at positive index/base t gives the genuine
F=t^t>=16^16>1, independently of all radix signs. Equation (5) implies y is
a nonzero multiple of F, with |y|>=F.

The radix identity q=4z+1 gives q!=0 and |q+1|>=2 immediately. Therefore the
q+1 pool can be interpreted FIRST, without knowing the sign of q or y.
It gives nonnegative actual representatives and a nonnegative derived label;
the retained anchor excludes a zero label. Consequently H=2+sum reps>=2.
The retained raw index row B mu=C+F+1 has positive right side, so B!=0.
Thus |BH|>=2. The singleton self-radix request gives x>=0 and q=(BH)^x.

If x=0, the last beta endpoint

    x=1+[1+(t+1)y]u_t

would make d=1+(t+1)y divide -1. Thus d=1 or d=-1. The former gives y=0;
the latter gives (t+1)y=-2. Both are impossible since y is a nonzero
multiple of F>1 and t>=16. This is the necessary adjustment to the parent's
positive-beta bootstrap: it excludes x=0 without assuming y>0.

Hence x>=1 and |q|=|BH|^x>=2. The q pool now has a nonunit base. In particular
its requested index y+1 is nonnegative. Thus y>=-1; because y is a nonzero
multiple of F>1, necessarily y>=F>0.

The parent's endpoint argument now resumes verbatim. If u0<=-1, then
x=F+1+(y+1)u0<=F-y<=0, impossible. Thus u0>=0 and x>=F+1. The last endpoint
then has u_t>=1, so

    x>=2+(t+1)y>=2+(t+1)F.                                (6)

All powers at q and q+1 have been authenticated. The common normalized
remainder norm gives short lifts, signed binomial recovery yields
B=binom(F+t,t)>0, and the self-radix equality now forces q>0. The source's
strict-range and all-primes CRT selector proof applies unchanged. The only
beta fact used there is y>=F and (6), both now proved in the correct order.

The exceptional boundary y=F is still excluded AFTER local row recovery:
the first local accumulator would be S0=0, the last St=1, while the positive
weighted local updates propagate zero. Thus y>F, the true first residue is
F+1, and every accumulator is positive. The unchanged multiplicity and
Horn-closure proof gives a finite C222 refutation. This proves soundness.

## 4. Every remaining arithmetic obligation and completeness

The strict parent's diagonal majorant and selector budgets are unchanged.
In particular Lambda_t=lcm(1,...,t)<=4^t, so F=t^t>=16^t>=Lambda_t². The
retained selector theorem requires R>=Lambda_t², not a strict inequality;
R=F is sufficient. It both isolates each local row with a prime power >t
and covers ALL prime powers dividing B for reverse CRT.

The diagonal label-uniqueness proof is also inherited, with its boundary
handled correctly. After discarding unit factors, unequal counts are
impossible because F+1>t^t. Once both counts equal d<=t, every coefficient
of each product of d factors 1+jX, 1<=j<=t, is a positive integer at most
binom(d,k)t^k<=t^d<=F. Although an individual coefficient can equal F, the
DIFFERENCE of corresponding coefficients has magnitude <F. Least-degree
reduction modulo F proves equality of the polynomials and all label
multiplicities. Strict local bounds only strengthen these estimates.

For completeness start with a finite C222 proof tree, and choose an even h
in the cofinal family t=16+h² strictly beyond its length and every local
parameter and derived label, including the truth-padding tuple. Choosing
h even is an existential witness choice, not a new guard on arbitrary
solutions. It makes t even and v_2(F)=t*v_2(t)>=t>v_2(t!). The parent's CRT
construction then gives arbitrarily large valid beta values

    y=F a², with a an odd multiple of the odd part of t!.

These can exceed every finite accumulator. They are allowed by (5), using
w=(a²-1)/2. Equivalently an old square-guard parameter w_old maps to
w_new=2w_old(w_old+1). This supplies the literal old-square-to-new-linear
witness map; no reverse map of every witness tuple is claimed.

All beta moduli remain odd; choose an arbitrarily large even x in the CRT
class. Since v_2(F+i)=v_2(i) for 1<=i<=t, B=binom(F+t,t) is odd. The parent's
parity-prescribing representative choices give odd H, so q=(BH)^x is an
odd square and hence is 1 modulo4. The z coordinate exists. Strict local
range divisibility, all primes, normalized tails and norm witnesses are
constructed exactly as in the source. Canonical Pell completion gives every
retained principal pair and frame/orientation witness. The converse of the
pooling lemma supplies the four new K,L coordinates. Thus the altered
arithmetic system has a zero whenever a finite refutation exists.

## 5. Exact algebra after the semantic step

The Pell-difference change is credited to source158. For each of fourteen
principal pairs replace X by D+AY (with the actual stored-coordinate offsets),
and subtract the sum of their retained Pell norm rows from the orientation
row. This is an integral affine coordinate bijection and an invertible row
operation. Its exact maps and inverses are checked; it reduces support but
not dimension.

Next use six certified common-Hessian-radical projections, credited to
source159. If d lies in the common kernel of every quadratic Hessian, then
R_i(u+s d)=R_i(u)+s L_i(d). A unit coordinate d_p=1 gives the integral shear
u_i=x_i-d_i x_p. If a selected slope L_j(d)=±1, its residual solves x_p as
an integer quadratic in the retained u coordinates. Substitution remains
quadratic because x_p appears only linearly after the shear. The resulting
map and restriction are inverse on integer zero sets. All six directions,
slopes, restored polynomials and forward/backward residual identities are
checked exactly, not inferred from a search score.

The odd-linear multiplier contraction removes one more coordinate and row.
Each final row-basis step R_i<-R_i+k R_j has inverse with -k, hence preserves
the common zero set. Squaring all rows and summing preserves that zero set
over Z. The frozen certificates reproduce the final equations without
running a search or optimizer.

## 6. Measured outputs and verification limits

| Endpoint | Variables | Rows | Terms | Height |
|---|---:|---:|---:|---:|
| integer217 | 217 | 154 | 25949 | 4576 |
| integer217_sparse | 217 | 154 | 14615 | 16866 |
| integer218 | 218 | 155 | 15631 | 4576 |
| integer218_sparse | 218 | 155 | 8817 | 16866 |

All degrees are exactly4, all residual coefficients have magnitude<=64,
and all coordinates occur. Each profile is nondominated by the other three
in the displayed four measures. The 218-variable low-height profile retains
one extra coordinate for less support at height4576; it is not redundant.
The two matched source branches each save eighteen variables and eighteen
rows. Source158's distinct225/162/7867/128446 endpoint has fewer terms than
these new profiles but more variables, rows and much larger height. None of
these comparisons is a global minimum claim.

The independent checker imports no producer, verifies every pooling and
frame identity, fourteen Pell coordinate inverses, six projection maps,
odd-linear contraction, inverse row operations, complete expansions,
liveness, exact metrics, and deliberate corruptions. A second independent
frame audit checks all seventeen actual power requests. Both normal Python
and Python -O are supported. Reconstruction uses frozen certificates in a
fresh temporary directory; no optimization or root search is run.
The retained parent ZIP pins the ordinary arithmetic and logical proof
closure; its original finite verification can be replayed separately with
`verify_all.py --parent`. Finite artifact checks do not prove unbounded
number theory or consistency, nor do they recompile the transitive formal
calibration.
