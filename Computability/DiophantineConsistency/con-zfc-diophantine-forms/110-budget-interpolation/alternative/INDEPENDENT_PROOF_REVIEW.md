# Independent review of the power-fusion tiling interface

Reviewed `PROOF.md`, `core.py`, and `check.py` on 24 October 2026.
The review checked the argument directly rather than deriving its correctness
from the finite regression suite. No mathematical gap was found in Theorems
1–3 or their conditional ordinary-polynomial contracts. This is an ordinary
mathematical review, not a proof-assistant check or external peer review.

## 1. Positivity before the geometric-power bootstrap

For arbitrary natural Q, the only unbounded Q contributions in all seven
linear rows are nonnegative: rows 2, 3, 5 and 7 have nonnegative Q coefficients,
and row 6 has constant Q-1. Negative coefficients are bounded below by
-max(P,C,1). Since H=4C^2P, every coefficient of every K_j is positive.
All constants c_j are at least -P, and G<P. Therefore
B-HG+c_j >= B-HP-P>0 under D>=32kA0 and P>=2. This proves F_j>=0 and
F_7>=Z before Q is bounded. It does not silently assume Q|P.

The implication Y<=A<L^8 then gives T_7<L. Its two nonnegative terms imply
both Q<2P and Z<L. Only afterward is the bottom L-lane extracted. Because
all other terms are divisible by L, the bottom lane is exactly Z; no prior
absence-of-carries assertion is needed.

## 2. Digits and no-carry inequalities

The bound |a_jt|<=H/2 follows from Q<2P and every color<C; the largest potential
term Q*s_t is below 2PC<2C^2P=H/2. The central and noncentral coefficient
bounds are valid. In particular G<P makes 2kHG<R/32 even at the endpoint
D=32kA0, P=2. Together with 2P<R/32, the central digit is strictly between
0 and R. The unguarded convolution degree is at most 2k-2, so its highest
base-R digit remains free for QL/(2P). The latter has integral coefficient
QR/(2P)=(D/2)QP^2<R, including the one-tile case k=1.

Consequently the seven masks force d_j=B. Row 1 then forces U=G, rather
than merely introducing another unconstrained linear combination. The
remaining six rows follow exactly.

## 3. Boundary geometry is recovered, not assumed

From (C-1)N0=Q-1 and (Q-1)W0=P-1>0, one gets Q>=2 and gcd(Q,N0)=1.
The equation QS0=PN0 therefore gives Q|P. Once P=C^N=2^(cN), write Q=2^u;
C-1|Q-1 gives c|u, and Q-1|P-1 gives u|cN. Thus Q=C^w with w|N, exactly
as needed for a rectangular board. The four boundary-mask expressions then
have the claimed row and column positions. The single-tile-per-cell argument
uses k<C to rule out base-C carries. Horizontal and vertical edge equations
are carry-free because each color is below C and each cell has one tile.

## 4. Three-graph interface

The odd quotient of (d+1)^A by d^Y has the parity of binom(A,Y), since every
binomial coefficient is below d=2^(A+1), and d is even. The remainder condition
e=s+t+1 is exact and excludes Y>A automatically. Substituting d=Pv forces
P to be a power of two; its residue modulo C-1 then makes it a power of C.
The bound A>=P and the enormous positive top lane ensure that d/P is an
integer, so completeness does not lose a tiling.

## 5. Second-order synchronization and the two-graph interface

The synchronization lemma is correct. If d|2^n and d-1|2^n-1, then d=2^u
and u|n, say n=uh. The second-order congruence says h=Y modulo d-1. Under
d>n+1, both h and Y belong to a common interval strictly shorter than d-1,
so they are equal. The example with d=2 correctly demonstrates why a size
restriction is necessary.

In the eight-coordinate certificate, n=(A+1)Y is positive before using a
power graph, since the positive offset already makes the packed Y>=1.
The parametrization d=P(n+v+1) forces d>n+1, and e=d(u+t+1) supplies d|e.
Thus synchronization gives e=d^Y, and injectivity of positive integer
Y-th powers yields d=2^(A+1). The remainder du+1 is strictly below e because
e-(du+1)=d(t+1)-1>0.

In completeness, s=1 modulo d implies u=(s-1)/d is a natural number.
Because s<e and d divides both e and s-1, e-d*u is a positive multiple of d,
so t=e/d-u-1 is also natural. The geometric sum defining j is at least Y
and is congruent to Y modulo d-1, proving both its integrality and sign.
Finally 2^(A+1)>A^3+A^2+A for A>=10, verified at A=10 and preserved by
induction, implies d>P((A+1)Y+1). Therefore v=d/P-n-1 is a natural number.
All eight advertised exposed coordinates are genuinely sufficient.

## 6. Degree and variable accounting

The highest mask lane has degree 48k. The highest guarded Y lane has the
same degree, since QL/(2P) has degree 6k and L^7 has degree 42k.
This validates deg(A),deg(Y)<=48k without treating registers as variables.

For the three-graph certificate, the largest fixed-base input degree is
96k, and the largest general-power input degree is 48k. For the two-graph
certificate, the degree bounds n:96k, d:96k+1, e:96k+2, W:96k+3 and
S:192k+3 follow by direct polynomial substitution. The stated final
sum-of-squares bounds are therefore valid.

The natural-variable counts 5+p2+b, 7+2p2+pg and 8+p2+pg correctly charge
separate internal witnesses for every graph occurrence. The report does not
claim that these graph polynomials have actually been supplied, nor that a
particular small ordinary Con(ZFC) polynomial follows from these interfaces.
Those limits are essential and are accurately disclosed.

## Editorial observations

The opening phrase 'two improvements' precedes three interface bullets and
can simply be changed to 'three interfaces'. A checker comment and diagnostic
range use d>n rather than d>n+1; this is harmless because the proof also works
under d>n (the interval [1,n] has width n-1), but aligning the wording would
make the relationship clearer.
