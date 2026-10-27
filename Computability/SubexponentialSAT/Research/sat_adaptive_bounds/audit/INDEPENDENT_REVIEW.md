# Independent mathematical review

Review date: 26 October 2026, Pacific time.
Reviewed repository snapshot: ProveIt `fd0edd17e6a29117179b40a453c0def59165bd7c`.

## Conclusion and scope

The new adaptive linear-flag separator theorem and the new centered
adaptive matrix-contraction theorem pass this independent mathematical
review. Their displayed leading coefficients, packing conditions, precision
buffers, recursive work accounting, and space accounting are consistent.
The results improve explicit normalized-wire upper-bound coefficients. They
do not improve the `s/sqrt(log s)` scale and do not prove a stronger SAT
logarithmic order. Neither result is formally verified in Lean or Rocq.

The review concerns the new arguments and their compatibility with the
stated imported interfaces. It is not a re-verification of every upstream
lemma in the ETH manuscript, or of the existence theorem for fast rational
matrix multiplication. Those dependencies remain explicit imports.

Reviewed proposed sections:

* `flag_section.tex`: adaptive linear flags and the rational decreasing
  alphabet schedule `16, 16, 8, 4, 4, ...`.
* `cached_results.tex`: entropy-ball consequence, adaptive triangle bound,
  recursively constructed group tables, and the generic/low-degree
  schedules.

## 1. Adaptive flags: proof review

For a descending complete binary linear flag F and a fixed nonzero
difference d, let V_F(d) be the flag subspace immediately before d leaves
the flag. A directed pair `(a,a+d)` occurs on the separator path to x
exactly when `a` belongs to the affine coset `x+V_F(d)`. For two flags and
two chosen leaves, the intersection of these endpoint conditions is empty
or is a coset of the corresponding homogeneous subspace intersection.
Its size is therefore at most the common-zero-leaf intersection. Summing
over d proves the claimed pairwise cut-set intersection inequality.

For the average path vector a over all flags through zero, every directed
pair incident to zero has coordinate 1. The general linear group acts
transitively on all ordered distinct nonzero pairs, so their coordinates
are equal. The known path size `2(r^2-1)/3` determines their common value
as `2/3`. Thus

    ||a||^2 = (r-1)(4r+10)/9.

For arbitrary nonnegative pair entropies, choosing one maximizing leaf for
each flag and averaging their path vectors gives z. Expanding `||z||^2`
and using the pairwise intersection inequality yields `||z|| <= ||a||`.
The minimum maximum path cost is bounded by its average over flags and
then by the imported weighted entropy inequality. Although z depends on
the entropy data, it belongs to a finite family determined only by the
fixed alphabet. This is enough for uniformity of the imported `o(1)`.

The exact selection algorithm compares integer products of list sizes.
It does not require reliable floating-point logarithmic comparisons.
The streamed separator identity charges the actual child contraction at
each leaf. Both levels of recursion can be traversed depth first, and
their indices and accumulators have polynomial bit size.

The resulting local coefficient is

    b_r = sqrt((r-1)(4r+10)/9)/r.

For `r=16` it is `sqrt(370/3)/16`, rather than `sqrt(170)/16` for the
previous fixed balanced tree. The claimed scoped optimality result is
also correct: the entropy vector proportional to a makes the path to its
distinguished zero vertex have the same required weight in every balanced
binary tree. This optimality is only for the stated Euclidean relaxation
and balanced separator-tree family. It is not a lower bound for actual SAT
instances or general contraction methods.

## 2. Flag schedule: parameter and work review

Write `Lambda = ceil(log_2 s) - ceil(sqrt(ceil(log_2 s)))`. The first three
retained ranges are `Lambda/80`, `Lambda/80`, and `Lambda/120`, up to
floors. The tail uses total budget `Lambda/60` and ratio `63/100`.
The cumulative ranges are therefore bounded successively by
`Lambda/40`, `Lambda/30`, and `Lambda/20` after depths 1, 2, and in total.

The relevant root symmetric exponent is

    2 log_2(16)/80 + 9/10 = 1.

The later retained-side exponents are

    4/40 + 9/10 = 3/30 + 9/10 = 2/20 + 9/10 = 1.

The inward `sqrt(log s)` margin makes these strict after the logarithmic
buffers and active-call factor `s/M <= log s` are included. The fresh-side
and packet-rounding exponents are at most `9/40`, `7/30`, and `1/4`.
All created degrees are below `s^(1/20+o(1))`, so the retained generic
degree bound remains valid.

The final child ratio is `1/2+o(1)`. Coarse shrinkage by `11/20` gives
depth at most `log_{20/11}(log s)+O(1)`. The minimum taper grows as a
positive power of `log s`, since `63/100 > 11/20`. Hence floors introduce
only uniform relative `o(1)`. The inherited-precision ratio is bounded
by `O(lambda^4 2^(-b))` with `b=ceil(6 log_2 lambda)`, and vanishes.

The sharp child sizes are `s`, `s/8`, `s/64`, and
`s/(256*2^(d-3))` in the tail, up to a uniform `1+o(1)` factor. Summing
the paid exponent yields

    C_flag = (pi sqrt(2)/ln 2) [
        (9 sqrt(80)/8) b_16
        + (sqrt(120)/64) b_8
        + sqrt(60) b_4 /
          (256 sqrt(1-q) (1-1/(2 sqrt(q)))) ],  q=63/100,

which is `46.18484558673077...`. The leading coefficient 46.19 is a safe
eventual value. Leaf work, immutable entry evaluation, interpolation,
description access, and products of polynomial factors are all lower order
on the stated scale. No uncharged oracle is used.

## 3. Entropy ball and centered adaptive triangle

The finite-net argument giving

    ||h|| <= (1+o(1)) K/r

from the fixed-vector weighted entropy estimate is valid. For every fixed
net resolution the error is uniform on a finite set; taking a limsup and
then refining the net establishes the uniform norm bound. This avoids
silently using a data-dependent vector inside a pointwise asymptotic claim.

For fixed block sizes, write `h = mu*1 + z`, with `z` perpendicular to the
all-ones vector. The partition minimizing total crossing entropy has total
at most `C mu`, by exact permutation averaging. Each crossing class has
entropy at least `m mu - sqrt(v)||z||`. Combining this with rectangular
matrix cost `sum H_i - (3/5) min H_i` gives

    (C-(3/5)m) mu + (3/5)sqrt(v)||z||.

Cauchy--Schwarz then proves the displayed squared coefficient
`(C-(3/5)m)^2/E + (9/25)v`. The inequality remains valid if the lower
bound on one class entropy is negative. Selection by minimizing an exact
product of list cardinalities implements the required rule.

## 4. Cached tables, work, and space

Building a block table by a binary tree really is a matrix contraction:
the shared indices are precisely the directed pairs joining its two child
blocks. Indices to the outside are disjoint. This includes all table
construction costs; the group caches are populated by paid recursive child
contractions.

For a merge with directed-axis counts `(v_1,v_2,v_3)`, the squared entropy
coefficient is at most

    v_1+v_2+v_3 - (21/25) min(v_1,v_2,v_3).

The factor `21/25` is `1-(2/5)^2`; the axis of smallest entropy receives
weight `2/5`, and its cardinality is at least the minimum axis cardinality.
The argument is uniform over the three possible smallest axes.

The exact ledgers are:

| Alphabet | Cache count | Largest merge score | Adaptive triangle score | Largest boundary count |
|---:|---:|---:|---:|---:|
| 9 | 16 | 916/25 | 162/5 | 36 |
| 15 | 28 | 2548/25 | 606/7 | 100 |

These are squared numerators before division by `r^2`. The largest merge
scores exceed the triangle scores. They give the stated beta coefficients;
the largest boundary coefficient is `2/3` in both cases. Matrix input,
output, intermediate tables, and the coordinate/CRT wrapper have storage
bounded by these boundary counts up to polynomial factors. Ancestor table
sizes add, rather than multiply.

The coordinate/CRT bridge remains an imported component. Its stated
mechanism is compatible with the coefficient ring: integer coordinate
products are reconstructed from sufficiently many nonexceptional odd
prime fields, then combined with the integral structure constants and
reduced modulo the working power of two. No inversion of a nonunit in
the original coefficient ring is required.

## 5. Cached schedules and constants

For the generic `r=9` schedule, total taper is at most twice the root
taper. The packing exponents are below one by a positive multiple of
`sqrt(lambda)`, and the new-side exponent is below `lambda/4`. Coarse
child shrinkage by `1/4` and leaf threshold `s/lambda^(3/4)` make the
minimum taper `lambda^(1/4+o(1))`. The inherited-precision ratio is
`O(lambda^(15/4)2^(-b))`, so the imported entropy estimate is valid.

Here `alpha=4/9`, `beta=sqrt(916)/45`, and the tail K ratio is `4/9`.
After the root, the full child-call path costs at most `4/5` times the
first tail K value. The resulting root child alternative has normalized
coefficient

    4/9 + 16/(45 sqrt(3)) < beta.

Therefore root local table work dominates all fully charged child paths.
This gives time coefficient `34.32528279728...` and space coefficient
`34.02417800749...`. The safe eventual values are 34.33 and 34.03.

For the low-degree `r=15` schedule, `A=113/1000`, `q=2/25`, and the root
taper is `2599/25000`. The exact inequality `450^113 < 2^1000` verifies
`A(1+2 log_2 15)<1`, covering old, fresh, and rounding degree gates.
The minimum taper diverges because `(25/2)^2 < 7^3` under the stated
leaf threshold. The recursive K ratio is `sqrt(2)/3`, and

    alpha/beta = 5/sqrt(91),
    sqrt(2)/3 + 5/sqrt(91) < 1.

Root local work therefore dominates. The exact squared constants, after
factoring out `pi^2/(ln 2)^2`, are `203840/23391` for time and
`200000/23391` for space. These agree with time `13.37964906627...` and
space `13.25302493301...`; safe eventual values are 13.38 and 13.26.
The smaller graph-degree premise is essential for this specialization.

## 6. What is still unproved

The new theorems do not close the pre-existing structured-mode summation
hypothesis behind the proposed `n log log n/log n` SAT exponent. They
also do not provide a low-degree, linear-wire representation of the compact
mode group tensors or a uniform `O(n)`-wire representation for arbitrary
clause density. Those would be order-level improvements and remain open
within the reviewed work.

The lower coefficients cannot be copied directly into a SAT-variable
bound: the chosen SAT reduction contributes its own wire expansion and
enumeration factors. They also cannot be numerically compared with an
unspecified constant hidden inside a different manuscript's big-O bound.
The broad statement that every proposal, including unproved hypothetical
rates, has been beaten would be incorrect.

## 7. Restricted multistage compression observation

Let a stage use the original collision-packing condition
`M_j >= 2 r_j^(4a_j) Delta_j`, with `a_j=2u_j`. Suppose that between
stages its whole mode sum is kept as one unfactored group tensor per
label, so the next graph has at most `r_j` nonisolated vertices. Average
degree then implies `Delta_(j+1) >= 2M_(j+1)/r_j`. Consequently

    8u_1 log_2 r_1 <= log_2 M_1,
    8u_j log_2 r_j <= log_2 r_(j-1),  j>=2,

and multiplication gives

    product u_j <= log_2 M_1 / (8^t log_2 r_t).

With only `a_j>=u_j`, replace `8^t` by `4^t`. This extends the previously
identified two-stage retained-range tradeoff to any number of stages in
that restricted architecture. It bounds the product of the nominal
square-root retained-range savings, not actual instance runtimes. It does
not apply automatically after further low-degree factorization, a different
packing theorem, or a genuinely new representation. If the compact graph
is subdivided to make it bipartite, the degree argument must be carried on
its original group vertices with the constant wire expansion included.
