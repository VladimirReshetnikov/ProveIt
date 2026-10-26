# Round23 signed affine horizons and affine-atom frames

## 1. The signed affine horizon theorem

Start at the incoming `ConZFC_Pell_Growth_210_2026-10-25` 210-coordinate
system. Its complete standalone-growth, affine-radix, signed-anchor, and
C222/ZF/ZFC source interfaces are retained. Put d=2^19. Replace only the
horizon equation by t=m(2z+1), for m=16 or m=4. Initially every coordinate
is an unrestricted integer. This is a semantic cofinal-source change,
not a claimed bijection with the old quadratic-horizon source.

Before classifying the standalone growth Pell equation, its divisibility
row already gives F=d*t*(2u+1), hence |F|>=d|t|>=dm and F is even and
nonzero. Thus y=F(2v+1) has |y|>=|F|. The square frame still contains the
actual F, and therefore W>=F^2+2>258. The source anchor theorem supplies
all canonical signed main Pell pairs before any signs are recovered.
Since C and F are even, D=2(C+F+1) is a nonzero even integer. Its retained
power request gives x>=0 and q=D^x. Because |t+1|>=m-1 and m>=4,
|1+(t+1)y| >= (m-1)dm-1 > 1. The terminal beta equation
x=1+[1+(t+1)y]u_t therefore excludes x=0. Thus x>=1 and |q|>=2.
The retained q-power with nominal index t now forces t>=0, hence t>=m.
This request is the actual `pow4.output` request at `index0`; it is
not a supposed q^(t+1) request.

For m=16, all remaining incoming proofs apply verbatim. Completeness
can use the incoming cofinal horizons t=16 mod 2^26; these belong to
16 mod 32, the new affine progression.

## 2. The m=4 threshold and completeness repairs

For m=4, positivity gives t>=4 and 4|t. The source constructor inequality
E(M,M)+1<=8(M+1)^2 holds for every nonnegative integer M, and constants
zero and one are below t. The same literal depth-19 trees therefore
have labels below L=8^(d-1)t^d. Positive-center Pell classification,
Y_n(4t+1)=n mod 4t and v2(Y_n)=v2(n) imply n>=dt exactly as in the
incoming proof. Consequently

    |F| >= (8t+1)^(dt-1) >= L^t.

The last comparison follows from (8t)^(dt-1)/L^t=8^(t-1)/t>=1 for t>=1.
These actual bounds imply |F|>2^64 and |F|>16^t already at t=4.
The later incoming bootstrap gives F>0, y>=F and x>=2+(t+1)y, hence
x>2^32 and 2+t+x+y+F<2x. Thus its literal local-polynomial estimate
Local<(2x)^(2^23)<2^x is unchanged. The elementary bound
lcm(1,...,t)<=4^(t-1), together with F>16^t, supplies the required
factorial-free selector radius. No unproved t>=16 estimate remains in
these uses. Four dividing t, even nonzero F, the radix parity, and the
ternary remainder budget are unchanged.

For completeness choose arbitrarily large t=4 mod 2^24 above the given
finite proof's length and parameters. Then t=4(2z+1) for an integer z,
v2(t)=2, and bit 21 of t is zero. Let n0=dt, y0=Y_n0(4t+1),
a0=X_n0(4t+1), and b0=y0/(dt). The original congruence and valuation
proof gives b0 odd and a0=1 mod4. Choose L0>24 with 2^L0>t and R=L0-21.
The incoming Pell-permutation lemma supplies a positive odd s with

    (t/4)*b0*Y_s(a0)=1 mod 2^R.

The same residue class has arbitrarily large positive indices. Put
F=y0*Y_s(a0), X=X_(n0*s)(4t+1), Z=tF and
u=(F/(dt)-1)/2. All growth rows hold and F=2^21 mod2^L0.
Since t<2^L0 and its bit21 is zero, F+t has no binary carries and
B=binom(F+t,t) is odd. The incoming squarefree prime-support beta
spacing, CRT, even cofinal C, radix and final main-Pell construction
now complete every witness in their original acyclic order.

## 3. Optional frame compression and difference orientation

This section is a further semantic source change, applied only where an
explicit endpoint certificate says so. A literal 34-atom ledger verifies
that the incoming frame is exactly W=2+sum a_j^2, where all actual bases,
indices and proposed outputs of all fifteen retained requests occur.
After t=m+2mz, every a_j is an integer affine form in ordinary front
coordinates; no private Pell coordinate occurs.

For L=c+sum a_i u_i, the elementary integer inequality
|a_i u_i|<=u_i^2+floor(a_i^2/4) gives
|L|<=sum_(a_i!=0)u_i^2+|c|+sum floor(a_i^2/4).
The exact ledger's largest constant is m^2+m+1 (from t+1). Replace the
frame by

    W=m^2+m+2+sum_(distinct underlying front coordinates) u_i^2.

The actual affine forms are retained in all power and index requests.
In particular |every actual atom|<W. More strongly, the same ledger
proves |every actual atom|<=(3m+1)sqrt(W): its largest absolute affine
coefficient sum including constant is 3m+1, attained at t+1 or F+t.
The coordinate F is among the underlying coordinates, so the preliminary
divisibility argument gives W>(dm)^2>=2^42 before all sign recovery.

The original power theorem's squared-atom hypothesis is NOT silently
reused. Here is its complete replacement estimate. Let s=ceil(sqrt(W)),
b=(3m+2)s, for m in {4,16}. Then every actual atom has absolute value
at most b, b<W, 4b+1<=W, and b^2<=10000W. These inequalities follow
from s<=2sqrt(W), m<=16 and W>=2^42; for example
4b+1<=400sqrt(W)+1<W. The exact negative-index-clearing argument in
the inherited pooled-power identity now gives, for at most 15 requests,

    0<=E=sum_i[m_i n^b-n^(b+k_i)]^2
          <=60 b^(4b)<W^(4b+1)<=W^W.

It also gives |T|>=2|A|-b^2-1>W^W, since |A|>W^W and
W^W>10000W+1. Hence E=0, recovering every integer power, including
unit bases; a nonunit base excludes a negative exponent. The same
argument with one summand covers retained singleton requests. Thus the
original Pell center need not be multiplied by four.

The anchor comparison first identifies the classified index |C|,
using |C|<W, and the cap bounds every other classified index by |C|.
In the orientation sum replace only

    (Y_(F+t)-(F+t))^2

by

    (Y_(F+t)-Y_t-F)^2,

retaining (Y_t-t)^2 and every abscissa error. The zero set of these
nonnegative error forms is unchanged. The exact quadratic delta is
supplied in the certificate and propagated to the delivered residual
basis. Reduced modulo A-1, the changed error has absolute value <3W;
the others have absolute value <2W and each abscissa error has absolute
value at most2. With 13 principal pairs, the nonnegative residue sum
is <57W^2+52<4W^3<|A-1|. The congruence therefore makes every error
zero, including first Y_t-t and then the missing F+t error. The |C|=1
exceptional branch is ruled out by the retained nonzero anchor error
and the same small-residue estimate before any comparison theorem at
that exceptional modulus is invoked.

Completeness still selects every arithmetic-front value first. It then
sets the new W and chooses the cofinal shared Pell center and private
anchor witnesses. Canonical errors make the new difference divisible
by A-1; all power quotients exist by the exact identities. No earlier
CRT modulus depends on W. All sign and arithmetic arguments in §§1-2
therefore remain valid.

## 4. Exact finite maps and growth-factor splitting

Substituting t=m+2mz into all other rows and deleting the horizon row
and t-coordinate is an integer zero-set bijection for the modified
source. Its inverse inserts that literal affine expression. This
includes frame, cap, orientation, power and growth rows, not merely
the arithmetic-front rows.

For nonnegative a_1,...,a_r with sum19, replace the divisibility row
F=2^19 t(2u+1) by unit definitions
w_1=2^a_1 t, w_2=2^a_2 w_1,... and
F=2^a_r w_(r-1)(2u+1). The new wires have unique integer values;
forgetting them and inserting their sequential definitions are inverse
on the zero sets. Every residual remains quadratic. Subsequent integer
coordinate shears/translations and elementary row operations are
explicitly invertible. These are exact algebraic changes, unlike the
cofinal-source and frame changes above.

For every final polynomial, the arithmetic proof plus these finite maps
and the pinned C222/ZF/ZFC calibration proves within ZFC that an integer
zero exists iff a finite ZFC refutation exists. No consistency assumption,
external-standard-code restriction, complete new proof-assistant build,
or global optimum claim is made.
