# An even affine horizon: a quartic in 209 unrestricted integers

## Result, comparison and exact source

The equation in `integer209/equation.json` is the sum of the squares of 149
literal quadratic residuals in 209 independently unrestricted integer variables.
Its collected polynomial has degree 4, 5,486 nonzero terms and coefficient height
17592186044416=2^44. The maximum residual coefficient is 4194304=2^22.
Every coefficient is supplied, with exact maps and an independent checker.

The immediate parent is the newly inspected Pell-growth210 equation from
snapshot c8187221a60df5baa0047c254a592a014491b60c. Its original archive is
retained unchanged as `inherited/Source210.zip`, SHA256
33fecaaa728d5f38608b8b0930c09b08dbe9a01e03f6269f092ec6142d72a0ee.
The exact parent stage is `equations/principal210/equation.json`, SHA256
20a2108353a3756ed7d1ddfdc71695131dcf0b6d94039988d9565ac48e6e1f0a.
It is copied byte-for-byte as `sources/parent210.json`.

The parent has 210 variables, 150 rows, 5,282 terms and height 2^40. This candidate
saves one variable and one row, at the cost of 204 additional terms and sixteen
times the height. It is a dimension/coefficient tradeoff, not dominance. The
separately verified 212-variable scaled-pair construction is unchanged and
retained as a method control. No global minimum or historical-priority claim
is made, and this bounded candidate is the final construction tested here.

The new ordinary proof, composed with the identified inherited calibration,
establishes in ZFC that this polynomial has an integer zero exactly when
there is a finite syntactic ZFC refutation. Negating gives nonsolvability iff
Con(ZFC). It does not prove consistency, inconsistency or a zero. The argument
is internal to ZFC, without a restriction to externally standard proof codes.

The credited incoming source supplies standalone Pell growth, its sharper
constructor majorant, the affine radix, dyadic residue permutation, squarefree
beta spacing, exact projections and all logical calibration. Those are not
rediscoveries. The new contribution is the even-affine horizon together with
the signed bootstrap, smaller-threshold estimates and changed cofinal parity
construction needed to remove its private root. Every unchanged row is
literally retained after one affine substitution and renumbering. No fresh
Lean/Rocq build is claimed; the full original ordinary-proof package is
retained, not represented as a complete compilable Lean dependency closure.

## The literal change and its semantic scope

Let delta=2^19=524288. The incoming construction has the actual horizon

    t=16+4h_old^2.

Replace it by

    t=4h+2,             h independently unrestricted.          (1)

The old root is coordinate 178 of the frozen 210-coordinate source and occurs
only in residual 125. Substitute 4h+2 for coordinate 0 in every other residual,
delete row 125 and coordinate 178, and renumber the retained coordinates.
Every residual stays quadratic. Exactly five retained rows change: the
relevant front endpoint row, shared frame row, orientation row, standalone
Pell product row and growth-divisibility row. The certificate gives their
full old/new coefficient arrays, not just these descriptions.

The inherited reduction also commutes with this relaxation: throughout all
six projection stages the old root stays private; the five radical directions
and restoration polynomials avoid both t and the root; the final affine
consequence uses only the local front rows 5 and 18. All 79 final invertible
operations avoid the horizon row/root and never change t. Thus applying the
semantic change to this authenticated optimized parent does not conceal a
previous use of the old horizon in another retained condition.

This is a semantic zero-existence change, not a bijection between arbitrary
old witness tuples: the old horizons are 0 modulo 4, the new horizons 2 modulo 4.
The retained physical-coordinate map sends new h to actual t=4h+2 and leaves
all other retained physical coordinates unchanged. On physical tuples with
t=2 modulo 4, its inverse is h=(t-2)/4. The omitted old root is not reconstructed.
The two directions of the consistency equivalence are proved below by
arithmetic extraction and a fresh cofinal witness construction.

Keep the original standalone center 4t+1, with existing coordinates F and
three private growth coordinates X,Z,u:

    Z=tF,
    X^2-16Z^2-8ZF=1,
    F=delta*t*(2u+1).                                      (2)

No enlargement to center 8t+1 is required. Keep the even representative C,
selector, affine radix and exact-power request

    B*eta=C+F+1,   D_radix=2(C+F+1),   q=D_radix^x.          (3)

The last equality is proof notation for its retained quadratic certificate.
All fifteen remaining requests, forty-five base/index/output ports, thirteen
principal pairs, anchor comparison rows and normalized digit rows survive.
The old square frame is retained exactly, including a harmless duplicate
t atom left over from the obsolete growth request. Its34 actual affine
atoms are fully reconstructed in `frame_certificate.json` before and after
substitution. Thus its equation remains W=2+sum(atom^2), and every actual
requested base, index and output has square less than W.

## Soundness: recover the horizon before using positive growth

From (1), t is never 0 or -1 and |t|>=2. The last row of (2) alone gives

    F!=0, F even, |F|>=delta*|t|>=2^20.                    (4)

No Pell classification at a positive growth center is used here. In
particular the actual frame contains F and has W>=2+F^2>258 even when t or F
is negative. The entire inherited signed C-anchor and orientation proof
therefore applies before any sign recovery. Briefly, its nonnegative cap
forces a nonzero anchor ordinate with absolute index|C|; squared Pell
ordinate divisibility and the comparison congruences identify that index
without assuming C positive. The other classified absolute indices are
strictly smaller than|C|. Reduction of the pooled orientation modulo A-1
then gives a nonnegative residue smaller than |A-1|, forcing every principal
pair to be its canonical signed pair. This uses only the retained actual
frame bounds and cap, which are authenticated coefficient by coefficient.
Consequently the inherited signed-power lemmas are available: a nonunit
base forces a nonnegative index and the genuine integer power.

Retain y=F(2v+1), so |y|>=|F|. Because C and F are even, C+F+1 is odd;
D_radix is nonzero even and has absolute value at least 2. Its power request
first gives x>=0. If x=0, the last endpoint

    x=1+[1+(t+1)y]ut

would make 1+(t+1)y divide -1. But t+1!=0 and

    |1+(t+1)y|>=|t+1||y|-1>=|y|-1>1.

Thus x>=1 and |q|>=2. The q-pool is now genuinely nonunit. Its retained
t and y+1 requests imply t>=0 and y+1>=0. Since t=2 modulo 4, t>=2.
A negative y would be at most -|F|<-1, so

    t>=2,             y>=|F|>0.                          (5)

This order is essential: positivity of t was not assumed to exclude x=0.
The rejected odd-affine horizon allowed t=-1,x=0,q=1 and failed exactly
here; `review/REJECTED_ODD_HORIZON.md` preserves that diagnostic.

Only now classify the standalone Pell equation at its positive odd center
4t+1. The growth estimate below gives |F|>t. If x=1, the first endpoint
x=F+1+(y+1)u0 would make the nonzero F divisible by y+1 while
|F|<=y<y+1, impossible. Thus x>=2. The last endpoint now has a positive
multiplier and ut>=1, giving x>=2+(t+1)y. Hence |q+1|>=3, so its pool is
legitimate. Its F+t request gives F+t>=0; together with|F|>t this forces F>0.
The C request gives C>=0 and the already established anchor nondegeneracy
gives C>0. Thus D_radix>0,q>0, and the first endpoint gives u0>=0 and x>=F+1.
No postponed arithmetic sign is used as its own premise.

## The original center and constructor bound work at t=2

Write X_n(a),Y_n(a) for the standard Pell sequences, with initial pair(1,0)
and recurrence X_next=aX+(a^2-1)Y, Y_next=X+aY. For a>=2, every nonzero
integer Pell ordinate has absolute value Y_n(a) for a positive integer n.
The identities

    Y_n(a)=n mod(a-1),
    Y_(2n)(a)=2X_n(a)Y_n(a)

give v2(Y_n(a))=v2(n) when a is odd: X_n is always odd and Y_n is odd exactly
when n is odd. Also Y_n(a)>=(2a-1)^(n-1).

For the actual square-shell constructors, the largest value on arguments
at most M satisfies

    E(M,M)+1=8M^2+14M+8<=8(M+1)^2.

At t>=2, every local parameter and every constant leaf 0 or 1 has
value-plus-one at most t. The unchanged authenticated maximum constructor
depth is 19. Induction therefore bounds every formula label strictly below

    L=8^(delta-1)*t^delta.                               (6)

This sharper bound needs only t>=2, not t>=16. It covers the same exact
fourteen outputs and nine schema trees as the preserved source ledger.

Equation(2) is X^2-((4t+1)^2-1)F^2=1. Let |F|=Y_n(4t+1). Because 4t divides F,
the first Pell congruence gives 4t|n. The odd multiplier in(2) and the exact
valuation give v2(n)=19+v2(t). Hence n/(4t) is a positive integer of exact
valuation 17, and n>=delta*t. Consequently

    |F|>=(8t+1)^(delta*t-1)>=(8t)^(delta*t-1)>=L^t.        (7)

The exact ratio of the last lower bound to L^t is 8^(t-1)/t>=1. In particular
|F|>t, as used only after (5) in the bootstrap. After F positivity has been
recovered, (7) is the weighted-label separation budget F>=L^t.

Two other small-threshold arguments must be updated explicitly. Since t>=2,
8t+1>=17 and delta*t-1>=t, equation (7)'s first bound gives

    F>=17^t>16^(t-1)>=lcm(1,...,t)^2.                    (8)

Thus the all-primes binomial selector remains valid at t=2. We do not reuse
the false small-threshold assertion t^t>=16^t. The same strong Pell bound
also gives F>2^32: delta*t-1>=8 and 17^8>2^32. From y>=F>t, t>=2 and x>=2+(t+1)y,
R0=2+t+x+y+F<2x. If 2^s<=x<2^(s+1), then s>=32 and

    2^23 log2(2x)<2^23(s+2)<2^s<=x.

The last inequality starts at s=32 and persists by induction. The inherited
literal local-degree bound therefore gives R0^(2^23)<2^x<=p^(ex), so the
same selected local congruences recover exact local rows.

## Complete arithmetic extraction and logical calibration

The unchanged C-cap makes every other nonnegative nominal index strictly
smaller than C. In particular F+t<C, all ordinary upper arguments are at
most C, and every needed lower digit index is at most x. Equation (3) gives

    D_radix=2(C+F+1)>2C,     q=D_radix^x>(2C)^x.

Every binomial coefficient in a retained digit is therefore at most C^x,
which is less than q/2^x. The geometric-series tail is less than its digit
denominator divided by 32 because x>=F+1>2^32. The common normalized remainder
norm bounds the competing remainder in the centered half interval. Their
congruence thus forces equality. For the first digit, the nonzero selector
quotient gives |B|<=C+F+1=D_radix/2<q/2. Its true positive binomial coefficient
is less than q/32. The digit congruence yields

    B=binom(F+t,t)>0.

The unchanged B-base power gives N=B^x, while B|D_radix from (3) gives N|q.
Thus all ten digit/range predicates, every local interval, and all local
precision assumptions are authenticated exactly as in the incoming source.
The all-primes selector (8) covers each row and every prime of B in both
soundness and completeness.

For labels bounded by L, equation (7) supplies the source's sharp product
separation theorem, including equality F=L^t. Unequal factor count s are
impossible because F+1>L^t. At equal count m<=t, each positive elementary
symmetric coefficient lies in[1,L^m] subset[1,F], so differences have
absolute value less than F. The least nonzero coefficient cannot disappear
on evaluation at F. Thus label multisets coincide. Zero labels contribute
units and are omitted. The unchanged boundary and positive-accumulator
arguments recover a finite single-conclusion Horn flow; the inherited
closure proof extracts a refutation even if the flow has cycles. In
particular any exclusion of y=F is made after local recovery, not before.

The literal local arithmetic uses the square-shell presentation. First apply
the retained injective square-shell/original-C222 recoding, which carries
finite refutations in both directions. This unchanged recoding precedes the
logical calibration; the shell labels are not silently identified with the
original numerical codes. The retained named endpoints are
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. They compose the
literal arithmetic extraction with a finite ZFC refutation. No machine
execution or Jones-polynomial specialization is substituted for these
calibrated endpoints. This proves soundness.

## Cofinal completeness with the changed dyadic bit

Start with a finite C222 refutation and all its finite local parameters,
proof length and padding. Choose a>=11 sufficiently large and set

    t=2^(2a)+2,        h=2^(2a-2).                       (9)

These horizons are cofinal and satisfy (1). They have v2(t)=1 and binary
bit 20 equal to zero, since their only nonzero bits are 1 and 2a>=22.
Put n0=delta*t, y0=Y_n0(4t+1), a0=X_n0(4t+1). The congruence gives t|y0,
and the valuation gives v2(y0)=20. Hence

    b0=y0/(delta*t)

is an odd integer. Also a0=1 modulo 4 because n0 is even and the abscissas
at odd center are odd.

Use the inherited normalized Pell permutation lemma: if a0=1 modulo 4,
s->Y_s(a0) induces a permutation modulo every 2^r. Here is its unbounded
proof. For H=2^r, the valuation gives v2(Y_H)=r. The norm and X_H=1 modulo 4
give X_H=1 modulo 2^(2r+2). Addition then yields

    Y_(s+2^r)(a0)-Y_s(a0)=2^r mod2^(r+1).

The two lifts of each index class have opposite next output bit. Induction
from parity proves bijectivity and periodicity; adding positive multiples
of 2^r gives cofinal indices in a selected class.

Choose b>22 with 2^b>t. Since (t/2)b0 is odd, the permutation supplies a
positive odd indexs, as large as desired, satisfying

    (t/2)*b0*Y_s(a0)=1 mod2^(b-20).

Set n=n0*s and

    F=y0Y_s(a0)=Y_n(4t+1),
    X=X_n(4t+1), Z=tF, u=(F/(delta*t)-1)/2.

All values are integral, F is positive and arbitrarily large, and every
row of (2) holds. These choices give

    F=2^20 mod2^b.                                      (10)

Below bit b, F has only bit 20, which is absent from t; at or above bit b,
t has no nonzero bits. Therefore the binary supports of F and t are disjoint.
The identity v2(m!)=m-s2(m) gives

    v2 binom(F+t,t)=s2(F)+s2(t)-s2(F+t)=0.

Thus B is odd. This changes the incoming bit 23 construction to bit 20, rather
than silently reusing its old t=16 modulo 2^26 horizon.

Choose an arbitrarily large positive odd w divisible by every odd prime <= t,
and put y=Fw. Every prime<=t divides y. If 1+iy and 1+jy had a common prime p
for 1<=i<j<=t+1, then p is coprime to y and divides j-i, so p<=t; but then p|y,
a contradiction. Hence all beta moduli are pairwise coprime. This uses
prime support, not the false assertion t!|y with fixed v2(F)=20. Choose w
large enough to dominate all pending-state values and then choose a positive
beta code x arbitrarily large in its CRT class. The odd-linear beta parameter
is(w-1)/2. Define N=B^x only after x is fixed; N is odd.

The generalized factorial-free selector (8) assigns the independent CRT
representatives modulo N^2. Choose the eight ordinary representatives
positive first. BecauseN^2 is odd, chooseC even, positive and cofinally
large in its prescribed class, exceeding all other requested indices and
representatives. The selector congruenceB|C+F+1 remains true. Only then
setD_radix, q and their exact powers. We haveD_radix>2C and N|q, so the
same digit bounds supply all normalized quotients and remainders.

Choose the shared square frame after all these arithmetic outputs are
fixed. Its canonical positive principal pairs, private even-C anchor
comparisons, cap slack and orientation quotient are completed exactly by
the retained source construction. All their hypotheses have just been
checked, without a cofinal-square horizon. Evaluate every ordinary circuit
wire, substitute the new h in(1), omit the old root slot and renumber.
This constructs an integer zero from every finite refutation and completes
the ordinary equivalence.

## Exact verification and portability

`semantic_certificate.json` pins the whole original210 equation, every
changed row, the exact substitution and the private root/row deletion.
`frame_certificate.json` independently reconstructs all 34 actual square
atoms and covers all 45 actual power ports. `coordinate_map.json` gives all
retained coordinates, rows and exact renumbering. The independent checker
imports neither producer nor producer algebra library. It compares every
row, verifies the inverse affine polynomial identities on retained physical
tuples, recollects every quartic coefficient and parses all 298 plain/TeX
residual displays back into polynomials. Actual-data corruption controls
must fail with and without Python -O.

Verification is read-only unless an explicit receipt path is supplied.
Every verification rebuilds from a fresh relocated copy and byte-compares
all generated JSON. The optional parent replay authenticates the original
archive, the immediate principal210 stage, its inherited source 173 closure,
all source 210 stages and the full original package verifier. New certificate
paths are relative; historical strings inside the unchanged original archive
are provenance, never paths used to find new inputs. No root search, remote
write or proof-assistant rebuild is involved. Finite checks certify literal
algebra and source binding, not the unbounded consistency theorem by testing.
