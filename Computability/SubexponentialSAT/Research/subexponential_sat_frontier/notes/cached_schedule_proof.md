# Cached 7/9 schedule: complete proof memorandum

## Result, scope, and novelty

Under the same normalized arbitrary Boolean tensor interface and inherited
algebraic dependencies as the polynomial-space theorem, a new explicit
retuning of the existing group-cache/three-block/Strassen construction gives

    time <= poly(s+L) 2^((37.93010908288456...+o(1))s/sqrt(log2 s)),
    space <= poly(s+L) 2^((33.62304092165775...+o(1))s/sqrt(log2 s)).

Consequently 38 and 34 are convenient eventual time and space coefficients.
This is not polynomial space. It does not improve the logarithmic order and
does not claim a numerical coefficient per SAT variable.

Caching, exact pair-weight indexing, three-block factorization, division-free
Strassen multiplication, and changing the root alphabet relative to the tail
are already in the incoming packets. The contribution is the new explicit
7/9 schedule and its complete resource proof, combining these ingredients
with asymmetric degree-aware packing and full-Cauchy modes. In particular,
the round-2 report already has a root/tail alphabet change, so such a change
alone must not be advertised as novel.

## Pairwise entropy and normalization

Near-unit common pair-label padding yields, for each directed pair g!=h,

    c_gh <= (2+o(1)) M/(r^2 D),

with sharp precision p<=(6+o(1))MD/u and full-Cauchy weight slope4.
For any fixed nonnegative pair weights w_e, the joint packet's weighted
generating-function proof therefore gives

    sum_e w_e h_e <= (sqrt(sum_e w_e^2/r^2)+o(1)) K(M,u),
    K(M,u) = (pi sqrt(2)/ln2) M/sqrt(u),

where h_e is the base-two logarithm of the exact-weight list size for pair e.
This is K=pi sqrt(2), not pi sqrt(6), because padded mass is now (1+o(1))M
rather than3M. No extra multiplier1-1/r is needed: diagonal pairs are absent
and their exact count is already in each displayed subset cardinality.

Exact weight arrays are polynomially numerous for fixedr, and tuple lists
can be counted/indexed by the joint packet's polynomial-size dynamic program.
Each group value is obtained by recursive child contraction, not by assuming
an inexpensive oracle. All polynomial factors retain fixed degree because
r belongs to the finite set{7,9}.

For blocks of sizes k_1,k_2,k_3, a block of size k has

    incident directed pairs: 2rk-k^2-k,
    boundary directed pairs: 2k(r-k).

The three block-pair classes have sizes2k_1k_2,2k_1k_3,2k_2k_3. Put
omega=log2 7 and e=omega-2. Rectangular Strassen costs the entropy-weighted
maximum with one class weighted by e and the other two by1; the worst case
discounts the smallest class. Table construction must ALSO be paid and can
exceed the Strassen term, as it does at the7-group root.

## Exact root and tail local coefficients

At the root use r=7 and blocks(2,2,3). There are12 pairs incident with a group,
at most30 incident with one block, at most24 crossing a block boundary, and
block-pair class counts(8,12,12). On scaleK(M,u):

    a_7 = sqrt(12)/7                         [child-cache enumeration],
    A_7 = sqrt(30)/7                         [table construction],
    B_7 = sqrt(24+8e^2)/7                    [Strassen contraction],
    J_7 = sqrt(24)/7                         [stored block table].

Here A_7>B_7. Thus the root's local nonrecursive work coefficient is
L_7=A_7=sqrt(30)/7=.7824607964..., NOT the smaller Strassen coefficient.

In the tail use r=9 and blocks(3,3,3). The respective cardinalities are16,
42,36, and(18,18,18). Therefore

    a_9 = 4/9,
    A_9 = sqrt(42)/9,
    B_9 = sqrt(4+2e^2)/3,
    J_9 = 2/3.

Here B_9>A_9, so L_9=B_9=.7676547213096726... . The formulas and strict
inequalities are checked using exact rational interval arithmetic.

## Strict rational schedule and packing gates

Let lambda=ceil(log2 s), H=ceil(s/lambda), b=6ceil(log2 lambda), and

    r_0=7, r_d=9 (d>=1),
    eta_0=89/5000,
    eta_d=(1233/125000)(7/25)^(d-1) (d>=1),
    u_d=floor(eta_d lambda),
    a_d=sum_(j<=d)u_j+(d+1)b.

The total leading capacity is

    89/5000 + (1233/125000)/(1-7/25) = 63/2000 = .0315.

The root symmetric-degree cap and all later retained-side caps are strictly
inside their boundaries because

    7^89<2^250  => 2*(89/5000)log2 7<1/10,
    9^63<2^200  => (63/2000)log2 9<1/10.

Below the root all original/retained vertices are on one side and fresh
packet vertices on the other, so R_d<=s^.9 and C_d<=2L_(d-1). The other
packing and rounding terms have powers bounded by

    2/10+63/2000=.2315<1.

New degrees are at most s^(.0315+o(1))<<s^.9. Fixed positive exponent margins
absorb the additiveO((log lambda)^2) capacity, active-size factor s/M<=lambda,
and all logarithmic factors in the asymmetric packing lemma.

For a noncircular bootstrap, first consider hypothetical depths
d<=ceil(log_4 lambda)+C and active sizesM>H. At those depths,

    min u_d >= lambda^(epsilon+o(1)),
    epsilon=1-ln(25/7)/ln4>0,

because25/7<4. All packing gates hold uniformly there. Every tail child has
at most(2/9+o(1))M<M/4 eventually. The root has only one exceptional prefix
level. Hence an active tail cannot reach the hypothetical depth limit,
closing the induction. Floors are uniformly negligible.

Padding errors areO(1/lambda) plus fixed-power vanishing terms, whose product
overO(log lambda) levels is1+o(1). Consequently

    M_0<=s,
    M_d<=(1+o(1))s(2/7)(2/9)^(d-1), d>=1.

The same additive-buffer proof as in the PS memorandum yields sharp
p_i<=(6+o(1))MD/u_d and uniformly vanishing entropy saddle. All algebraic
identities retain the creation-time lift convention. Changingr changes only
fresh labelings and local grouping, not earlier tensor definitions.

## Full time recurrence

Write Kstar=pi sqrt(2)/ln2, x=89/5000, y=1233/125000, and

    k_0=Kstar/sqrt(x),
    k_1=(2/7)Kstar/sqrt(y),
    gamma=(2/9)/sqrt(7/25)=10/(9sqrt7).

Then on the globals/sqrt(lambda) scale, the call entropy factors are
k_0 at the root and k_1 gamma^(d-1) in the tail. Suppressing polynomial
factors and uniformo(1) perturbations, the recurrence is

    T_0 <= 2^(a_7 K_0) 7T_1 + 2^(L_7 K_0),
    T_d <= 2^(a_9 K_d) 9T_(d+1) + 2^(B_9 K_d), d>=1.

For the tail,

    a_9/(1-gamma)=.7662313756800506... < B_9=.7676547213096726... .

Therefore all tail matrix-work and child-cache paths are bounded by
B_9 k_1 on the global scale. Explicitly, at tail depthj>=0 their coefficient
is

    a_9 k_1(1-gamma^j)/(1-gamma)+B_9 k_1 gamma^j
       <= B_9 k_1.

After paying the root's cached-child enumeration, the whole time coefficient
is thus

    C_time = max(L_7 k_0, a_7 k_0+B_9 k_1).

Its two alternatives are, respectively,

    37.59170255554195907609...,
    37.93010908288455996710... .

The first tail call controls total time; the root's table construction is
slightly cheaper. This maximum, not a sum of root and child matrix costs,
follows from the additive recurrence. Root caching enumeration DOES add to
every child path and has been paid explicitly.

## Space, bit cost, and nonleading work

At the root and first tail depth the table storage coefficients are

    J_7 k_0 =33.62304092165775367105...,
    J_9 k_1 =12.29287807841361204510... .

Later table coefficients geometrically decrease. Individual group caches
are smaller than the corresponding block tables. The sum of stored ancestor
caches/tables acrossO(log lambda) stack frames has the maximum of these
exponential coefficients pluso(1), so root storage controls space.

Use the incoming joint packet's explicit sequential-record/tape scheduling
for cache access and its division-free rectangular Strassen implementation.
The latter is valid over the same commutative quotient ring. Polynomial-size
record contents, exact pair-weight indexing, sorting/reblocking, field
arithmetic, andO(log lambda) recursion overhead do not change the coefficients.
Original entry evaluationexp(O(s^.9)), packet entriesexp(s^(.0315+o(1))),
leaf2^O(s/lambda), and polynomial branching overhead all remain lower order.
The input description-length factor is a fixed polynomial as before.

## Exact verification and comparisons

verify_cached_schedule.py imports the interval primitives from
verify_heterogeneous_schedule.py. It bracketspi with Machin's formula,ln2
by a positive series, andomega by

    omega=3-2atanh(1/15)/ln2.

Square roots use integerisqrt brackets. All feasibility and recurrence gates
are exactFraction comparisons, and run identically underpython andpython-O.
It proves

    37.93010908288 < C_time < 37.93010908290 < 38,
    33.62304092165 < C_space < 33.62304092167 < 34.

The straightforward prior composition of asymmetric fixed-r16 scheduling
and joint-Cauchy cache/Strassen gives time44.53757185496246. Its parameter
boundary improves this to44.26179476465665. A stronger comparison is obtained
by retuning the existing fixed-r asym family to8 and taking its cap boundary:
time38.16774569701537, space33.99270106370396. The new strict7/9 schedule
improves that time coefficient by about.622611%, with a slightly lower space
coefficient too. The38.1677 comparator is an optimization-envelope value,
not a claimed lower bound or a proven optimum over all imaginable schedules.

The earlier distinct49-pageeth.pdf does not expose a directly comparable
explicit coefficient for this normalized interface, so no numerical
dominance over its unspecified constant should be asserted. Stronger
low-degree specializations are likewise separate and can be retained in a
portfolio. Nothing here resolves the unprovedn/logn summation interfaces.
