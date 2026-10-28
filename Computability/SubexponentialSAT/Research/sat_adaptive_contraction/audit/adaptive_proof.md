# Adaptive three-block contraction: proof and integration notes

This is a new refinement relative to the reviewed ProveIt corpus. It imports
the exact deformation/recovery/child-network framework, the asymmetric
nearly lossless packing lemma, and the full crossing-orientation Cauchy basis.
It changes the mode-graph partition *after* an exact pair-weight allocation
has been fixed. No new global SAT order is claimed.

## 1. Local notation and inherited inputs

Take r=9 groups. At an active call let M be the wire count, u its retained
valuation range, D=L/2^i, and P=(1+o(1))M the padded mass. The inherited
precision refinement gives p_t <= (6+o(1)) MD/u. The joint Cauchy modes have
weights at least 1+4q-2 popcount(q). Each directed group pair has at most
2P/(81D) modes of any index q. All o(1)'s are uniform in active calls under
the schedule in Section 5 below.

For each exact nonnegative weight array (b_gh) with sum b_gh < p_t, let d_gh
be the number of mode exponent tuples of exact weight b_gh on the directed
pair g->h. Skip the array if any d_gh=0. Otherwise set h_gh=log2 d_gh.
Exact counts and indexing are supplied by the ordinary unbounded-knapsack
dynamic program, polynomial in the number of modes and p_t. Their integer
bit lengths are polynomial. There are at most (p_t+1)^72 arrays, so this
outer enumeration is polynomial for fixed r=9.

Put K = (pi sqrt(2)/ln 2) M/sqrt(u). For a fixed set I of directed pairs,

    sum_{e in I} h_e <= (sqrt(|I|)/9 + o(1)) K.                 (1)

Proof: use a common exponential parameter theta for the pairs in I. The
slope-four generating product satisfies F(theta)=pi^2/(24 theta)
+O(log^2(2/theta)). Consequently

    ln2 sum_I h_e <= theta p_t
        + |I| [2P/(81D)] pi^2/(24theta)
        + O((M/D) log^2(2/theta)).

Optimize the first two terms using the prescribed upper envelopes, not an
individual large-budget asymptotic for every pair. This yields (1). The
actual budget of a pair can be zero. There are only finitely many possible
subsets I, so the same error bound covers a subset selected adaptively.

The group factor Z_g depends only on the 16 directed pair indices incident
with g. Its value is a recursive child contraction, not a free oracle.
The old tensors retain their immutable creation precisions and canonical
lifts. Changing the partition does not change any tensor or its lift.

## 2. The new partition lemma

There are 9!/(3!^3 3!)=280 partitions of nine groups into three unordered
triples. For such a partition P, let E_cross(P) be its directed crossing
pairs. Select a partition minimizing the exact positive integer

    C(P) = product_{e in E_cross(P)} d_e.

Only 280 polynomial-bit products and comparisons are needed. This avoids
floating-point logarithms. In a uniformly chosen partition, any particular
directed pair crosses with probability (9-3)/(9-1)=3/4. Averaging gives

    log2 min_P C(P) <= (3/4) sum_all h_e
                    <= (1/sqrt(2)+o(1)) K.                 (2)

The last step uses (1) with 72 directed pairs:
(3/4) sqrt(72)/9 = 1/sqrt(2). This is the key new saving. A fixed partition
cannot use the averaging inequality for each instance of the pair lengths.

The exact finite counterpart is

    min_P C(P)^4 <= (product_all d_e)^3.

The checker verifies it using arbitrary integer dimensions and no logs.

## 3. Fully costed local algorithm

First cache each Z_g on all its incident pair-index assignments. Since a
group is incident with 16 directed pairs, this takes at most

    poly(s+description_length) 2^((a+o(1))K) child calls,
    a = 4/9.

For each of the three selected triples B, build its boundary table by
summing the product of its cached Z_g values over all internal pair indices.
A triple is incident with

    2*r*3 - 3^2 - 3 = 42

directed pairs and has 2*3*(9-3)=36 boundary pairs. Thus its construction
cost is at most 2^((beta+o(1))K), where beta=sqrt(42)/9, and its storage is
at most 2^((j+o(1))K), where j=2/3. These bounds hold for *every* triple,
including the adaptively selected ones.

Finally enumerate all assignments to the crossing indices and multiply the
three stored table entries. Equation (2) bounds this direct triangle sum by
2^((1/sqrt(2)+o(1))K), strictly less than the table construction envelope,
since 1/2 < 42/81. No matrix multiplication theorem is needed.

The resulting recurrence, suppressing polynomial factors, is

    T_d <= 2^((a+o(1))K_d) * 9 T_{d+1}
           + 2^((beta+o(1))K_d).                           (3)

Space at a call is at most 2^((j+o(1))K_d). The individual group caches
are smaller (a<j), and exact weight arrays are processed one at a time.

The included Python code uses dictionaries as a transparent RAM prototype.
For the bit-operation theorem, arrange each table and group cache in the
restriction of the boundary-first, internal-last lexicographic axis order.
Projecting a lexicographic scan onto a subset of its axes advances, repeats,
or rewinds a suffix. The total records crossed by a rewind can be charged
to the assignments of that suffix just scanned. With at most 72 axes,
sequential access therefore costs polynomial overhead per enumerated tuple.
The same argument applies to the direct crossing scan. This is the access
argument already used by the previous fixed-partition mode-graph theorem.

## 4. Exactness

Every global mode tuple belongs to exactly one exact weight array. Given an
array, its pair states form a Cartesian product. Caching does not alter a
group factor. The three block tables sum over disjoint sets of internal pair
states. Their product, summed over the crossing states, is the original
finite mode-graph contraction by distributivity in the coefficient ring.
Only addition and multiplication are used, so characteristic two, higher
powers of two, nilpotents, and negative intermediate representatives cause
no problem. The upstream Hermite recovery is unchanged.

## 5. An integer schedule attaining the boundary constant

Let lambda=ceil(log2 s), g=ceil(sqrt(lambda)), and

    B_lambda = max { b>=0 integer : 9^(20b) <= 2^lambda }.

This is computable with integer comparisons and has value
lambda/(20log2 9)+O(1). Let b_buf=ceil(6log2 lambda),

    u_0 = B_lambda - g,
    u_d = floor(u_0 / 2^d),
    a_d = sum_{j=0}^d u_j + (d+1)b_buf,
    H = ceil(s/lambda).

Use direct contraction for the bounded exceptional sizes where needed
parameter inequalities fail. The formula is stated only for sufficiently
large s, so u_0 is positive.

For a noncircular applicability proof consider hypothetical active calls
M>H at depths d<=ceil(log_4 lambda)+1. Uniformly in this range,

    u_d = (1+o(1)) lambda/(20log2 9 * 2^d),
    u_d = Omega(sqrt(lambda)),
    a_0 <= B_lambda - g + O(log lambda),
    a_d <= 2B_lambda - 2g + O((log lambda)^2).

The coarse lower bound for u_d absorbs the additive one in the hypothetical
depth range. At the root R=C<=ceil(s^0.9), Q=9^a0. Therefore

    log2(Q^2 C) <= lambda - Omega(sqrt(lambda)).

Below the root R<=ceil(s^0.9) and C<=2L_{d-1}. The retained-row constraint
has the same gap:

    log2(Q R) <= lambda - Omega(sqrt(lambda)).

The fresh-side and rounding powers satisfy

    log2(Q^2 C), log2(LQ^2)
       <= [ (1+2log2 9)/(10log2 9) + o(1) ] lambda,

whose leading coefficient is about 0.23155<1. New packet degrees remain
below s^0.9. These gaps absorb every fixed power of lambda, including
s/M<=lambda and the conditional-potential overhead. Hence nearly lossless
padding holds uniformly, and every child has at most (2/9+o(1))M wires,
in particular at most M/4 eventually. Thus active paths have depth less
than log_4 lambda+O(1), validating the hypothetical range and the induction.

The additive precision buffer gives D>=2^(a_{d-1}+b_buf+1). The inherited
precision bound O(s lambda^2 2^a_prev), divided by MD/u, is O(lambda^-2).
The polynomial jet-evaluation loss is also negligible. The precision
estimate p_t<=(6+o(1))MD/u and the subset entropy estimate are therefore
uniform. All precisions and interpolation degrees stay polynomial in s.

Set

    kappa = pi sqrt(40log2 9)/ln2,
    gamma = 2sqrt(2)/9.

Then K_d <= (kappa+o(1)) gamma^d s/sqrt(lambda), with harmless uniform
geometric perturbations. Unrolling (3), the exponent for work first done
at depth d is bounded by

    kappa [ a(1-gamma^d)/(1-gamma) + beta gamma^d ].

The bracket is at most beta because

    a/(1-gamma) = 4/(9-2sqrt2) < 2/3 < sqrt42/9 = beta.

The first inequality follows from sqrt2<3/2. Leaf enumeration, all entry
costs allowed in the normalized interface, and polynomial per-call work
are lower order. Thus

    T <= poly(s+description_length)
         2^((36.75031252383623...+o(1)) s/sqrt(log2 s)),
    S <= poly(s+description_length)
         2^((34.02417800749051...+o(1)) s/sqrt(log2 s)).

The exact coefficients are kappa sqrt42/9 and 2kappa/3. Values 37 and 35
are safe eventual coefficients. They can be certified using pi<22/7,
ln2>6931/10000 (four terms of its atanh series suffice), and log2 9<16/5
(9^5<2^16); the checker verifies the final rational inequalities.

For comparison, the same r=9 boundary schedule with the previous fixed
balanced partition and Strassen theorem has coefficient 39.1782313292...
The adaptive partition changes this upper-bound coefficient to36.7503125...
The best fixed r=8 composition discussed during review gives38.1677457...
at its boundary. These are upper-bound comparisons, not runtime ratios.

## 6. Executable evidence

`adaptive_blocks.py` is a complete local algorithm; `check_adaptive_blocks.py`
compares it with literal contraction over integer rings and moduli 2,16,257.
It verifies all 280 partitions, every pair's exact separation frequency,
all block incident/boundary counts, 160 exact-dimension averaging cases,
240 full local contraction cases, cached child-call counts, empty domains,
and seven invalid-input controls. The output ledger is reproducible under
ordinary Python and `python -O`.

The fixed-partition adversarial dimension fixture has d_e=2 on the54
directed crossing pairs of a given three-triple partition and1 on its
internal pairs. Repartitioning into transversals decreases the crossing
enumeration from2^54 to2^36, an exact operation-count factor2^18. No such
huge contraction is executed, and this is not a measured SAT speedup.

## 7. Source anchors

- `incoming_extracted/eth_asymmetric_packet_balancing_2026-10-26/eth_asymmetric_packet_balancing_2026-10-26/report.tex`:
  two-stage pair-load theorem, nearly lossless padding, side-degree invariant,
  exact crossing-family count, additive precision buffer.
- `incoming_extracted/eth_joint_cauchy_2026-10-26/eth_joint_cauchy_2026-10-26/report.tex`:
  group-preserving slope-four modes, exact pair-weight arrays, subset entropy,
  group-cache and block-table construction, sequential-access cost argument.
- `ProveIt/lib/openai-math/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex`:
  unchanged deformation, Hermite identity, child-network construction,
  creation-precision convention and normalized tensor interface.

No new formal-assistant certificate or complete SAT solver has been built.
The global density-sensitive SAT reductions remain inherited. The result
improves a leading normalized contraction coefficient and spends
subexponential space; it does not change the logarithmic order in n.

## 8. Additional low-degree specialization

Suppose the root maximum degree is at most ceil(s^(1/12)). This stronger
graph premise includes the usual bounded-degree clause networks eventually;
the coefficient is still per normalized wire count, not per SAT variable.

Set q=17/50, A=1/log2(162), and use the integer capacity

    B_lambda = max { b>=0 integer : 162^b <= 2^lambda }.

Let W=B_lambda-ceil(sqrt(lambda)) and

    u_d=floor((33/50) W (17/50)^d),
    a_d=sum_{j<=d} u_j + (d+1)b_buf,
    b_buf=ceil(6log2 lambda), H=ceil(s/lambda).

These are exact rational/integer operations. The total retained-range
budget is at most W and therefore
a_d<=A lambda-Omega(sqrt(lambda)) uniformly at depth O(log lambda).
All old tensor degrees are bounded by

    max(ceil(s^(1/12)), 2L_{d-1}),

because packet lengths increase with depth. The nearly lossless packing
conditions follow from the following two cases. If the original degree
term is the larger one, its exponent is at most
2log2(9) A+1/12<1, since 1/12<A. If a packet degree is the larger one,
its exponent is at most (1+2log2 9) A=1, with a subtractive
Omega(sqrt(lambda)) margin from the guarded capacities. The rounding term
LQ^2 has the same guarded capacity, because 1+2log2 9=log2(162).
Thus Q^2 max_degree polylog(s)=o(M), and the weaker asymmetric row condition
also follows. Fresh tensor degrees are at most s^(A+o(1))<s^0.9.

For the noncircular depth argument, consider depths through
ceil(log_4 lambda)+1. Since q=17/50>1/4,

    u_d >= lambda^(1+ln(q)/ln(4)+o(1))
         = lambda^(0.2218033257...+o(1)),

which tends to infinity. The same packing argument yields child size at
most M/4 eventually and hence validates the hypothetical range. Precision,
feature evaluation and leaves are treated exactly as before.

The new K_d has leading root constant and geometric ratio

    kappa_low = (pi/ln2) sqrt(100 log2(162)/33),
    gamma_low = (2/9) sqrt(50/17).

The cached-child path is still smaller than block construction:

    (4/9)/(1-gamma_low) < 18/25 < sqrt42/9.

For an exact check, gamma_low^2=200/1377<(31/81)^2, so the first
quantity is less than (4/9)/(50/81)=18/25. Squaring establishes the
second inequality. Therefore

    C_time,low = kappa_low sqrt42/9 =15.39193319879786...,
    C_space,low = 2 kappa_low/3 =14.25016112980349....

Safe eventual coefficients are16 for time and15 for space. They follow
from the same rational pi/ln2 bounds and log2(162)<37/5 (162^5<2^37).
The exact rational inequalities are included in the checker. These new
low-degree constants are compared only with bounds under the same input
degree premise.
