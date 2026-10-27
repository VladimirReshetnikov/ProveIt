# Independent order-improvement investigation

Source scope: ProveIt `f898a9fde4c3ed3bbcd53ed45cc79970b7b41d66`; all four incoming packets extracted under `incoming_review/`. This note is original analysis for the current review. It does not assert a stronger unrestricted SAT complexity order.

## 1. Main result: arbitrary asymmetric Hermite multiplicities do not improve the precision certificate

The prior `3sat_precision_refinement/report.tex` solves a real minimax problem for **valuation-symmetric** multiplicities and obtains leading normalized loss `6M/u`. The prior `3sat_asymptotic_analysis/audit/TAPER_AND_NEWTON_LEMMAS.tex` explicitly leaves asymmetric selection of nodes outside its barrier. The theorem below closes that particular loophole for the independent-jet Hermite precision certificate, and gives an exact finite minimax formula that includes highest-jet evaluation loss.

This is a lower bound on a specified precision certificate, not a lower bound on SAT, tensor contraction, arbitrary recovery identities, or recovery exploiting correlations among attainable jets.

### 1.1 Definitions and the exact top-jet loss

Let `a >= u >= 1`, `N=a+1`, `L=2^a`, and let `S` be any complete integer residue system modulo `2^N` containing `0`, such as `{-L,...,L-1}`. Assign arbitrary nonnegative integer multiplicities `q_t` to `t in S\{0}`, put `q_0=0`, and require `q_t=0` whenever `v_2(t)>=u`. No equality or monotonicity between different nodes is assumed.

For an active node `t`, write `i=v_2(t)`, `D_t=2^(a-i)`, and

`E_t(T) = product_{v in S\{0,t}} ((T-v)/(t-v))^(q_v)`.

In the usual Hermite reconstruction of `F(0)` from jets of `F(t+2^N z)`, the coefficient of the **highest raw jet** `[z^(q_t-1)]F(t+2^N z)` is exactly

`E_t(0) (-t/2^N)^(q_t-1)`.

Indeed, the reciprocal of `E_t(t+2^N z)` has constant coefficient one, so this raw jet enters no lower-degree term and enters the top term with coefficient one. Its negative two-adic valuation is

`Lambda_t(q) = sum_{v != 0,t} q_v (v_2(t-v)-v_2(v)) + (q_t-1)(N-i)`.

This is also the exact worst coefficient loss in the fixed Hermite recovery block at node `t`. Indeed, the truncated reciprocal of `E_t(t+2^N z)` has integral coefficients, while among the multipliers `E_t(0)(-t/2^N)^j` the worst valuation is at `j=q_t-1`. Therefore every raw-jet coefficient has loss at most `Lambda_t(q)`, and the highest raw jet attains equality. The exact nondecreasing independent-error block certificate is thus `p+max(0,Lambda_t(q))`. Normalize the additional charge by `D_t`, and set

`H(q) = max(0, max_{t:q_t>0} Lambda_t(q)/D_t)`.

The expression `Lambda_t(q)` is affine in all multiplicities. It can also be evaluated at inactive nodes as an auxiliary affine function, even though no jet is requested there. We extend it to nonnegative real multiplicities solely to study the relaxation.

For `1<=k<=N`, let

`S_k(t) = sum_{v: v == t mod 2^k} q_v`.

A direct valuation count gives the exact identity

`Lambda_t(q) = sum_{k=i+1}^N [S_k(t)-S_k(0)] - (N-i)`.    (1)

Proof: express each valuation as a sum of indicators of congruence modulo `2^k`, for `1<=k<N`. Excluding `v=t` subtracts `(N-1-i)q_t`. The highest-jet term adds `(q_t-1)(N-i)`, leaving `q_t-(N-i)`; the `q_t` is exactly the depth-`N` class mass, since `q_0=0`.

### 1.2 Inactive nodes can be included in the convex objective

Fix a nonempty valuation annulus `v_2(t)=i`. Within its binary residue subtree, choose a leaf maximizing the path sum `sum_{k=i+1}^N S_k(t)`. A maximizer can be chosen to have positive multiplicity. If an inactive leaf were a maximizer, compare it to an active leaf inside the smallest ancestor of that leaf that contains any positive mass. Above that ancestor the path sums agree; below it, the original leaf has zero subtree masses and the active leaf has a positive last mass, strictly improving the sum.

The remaining terms in (1), and `D_t`, are constant throughout the annulus. Thus its maximum affine loss is attained at an active node. An entirely empty annulus has every `S_k(t)=0`, so (1) is strictly negative. Consequently

`H(q) = max(0, max_{t in S\{0}} Lambda_t(q)/D_t)`.    (2)

This is a convex function of the full multiplicity vector, including for nonnegative real multiplicities.

### 1.3 Symmetrization theorem

Let `G` be the finite group of automorphisms of the complete rooted binary residue tree that fix the leaf `0`. It preserves `v_2(t)` and `v_2(t-v)`. It acts transitively on the leaves in every annulus `v_2(t)=i`.

For every such automorphism `g`, the permuted multiplicity vector has the same objective: `H(gq)=H(q)`. Averaging over `G` gives the valuation-symmetric vector `bar q_t = qbar_i`, where `qbar_i` is the arithmetic average of multiplicities in annulus `i`. By convexity of (2),

`H(bar q) <= average_g H(gq) = H(q)`.    (3)

The averaging preserves the total multiplicity and the allowed valuation levels. Therefore **asymmetric node choices cannot improve the real minimum of this fixed Hermite recovery certificate**.

The statement concerns the coefficient valuations, not invariance of the polynomial deformation under these tree automorphisms. No such invariance is needed: the Hermite coefficient valuations depend only on the preserved ultrametric distances.

### 1.4 Exact finite minimax recurrence

For a symmetric profile write `q_i` for the common multiplicity on annulus `i`, `D_i=2^(a-i)`, and `n_i=N-i`. Let `q_i=0` for `i>=u`. The normalized exact loss is

`Lambda_i/D_i = (2-1/D_i)q_i - sum_{j=1}^{u-1-i} j 2^(-j) q_{i+j} - n_i/D_i`.    (4)

For example, this follows from the standard finite-grid normalization loss plus the highest-jet evaluation term; the omitted infinite tail is `(n_i+1)q_i/D_i`, leaving exactly (4).

Fix required normalized multiplicity mass

`W = (1/L) sum_t q_t = sum_{i=0}^{u-1} 2^(-i) q_i`.

Define the following rational quantities backwards, taking empty sums as zero:

`r_i = [1 + sum_{j=1}^{u-1-i} j 2^(-j) r_{i+j}] / (2-1/D_i)`,

`c_i = [n_i/D_i + sum_{j=1}^{u-1-i} j 2^(-j) c_{i+j}] / (2-1/D_i)`.

Put `R=sum_i 2^(-i)r_i`, `C=sum_i 2^(-i)c_i`.

**Exact relaxed optimum.** Over all nonnegative real node multiplicities with total mass at least `LW` and the stated allowed levels,

`min H(q) = eta_* = max(0,(W-C)/R)`.    (5)

When `W>=C`, an optimizer is the symmetric profile `q_i=eta_* r_i+c_i`. When `W<C`, scale the profile `c_i` by `W/C`.

**Proof.** Symmetrization reduces the infimum to symmetric profiles. If `H(q)<=eta`, (4) implies

`q_i <= [eta+n_i/D_i+sum_j j2^(-j)q_{i+j}]/(2-1/D_i)`.

Backward induction gives `q_i<=eta r_i+c_i`, hence `W<=eta R+C`. This proves the lower bound (5). The displayed profile attains equality in every constraint when `W>=C`. When `W<C`, scaling `c` by `W/C` leaves every loss in (4) nonpositive, so it attains the zero optimum.

**Integer consequence.** Ceil each component of an optimal symmetric real profile. The required mass cannot decrease. A change `0<=delta_i<1` increases (4) by at most `(2-1/D_i)delta_i<2`, since all other changed coefficients enter with a negative sign. Thus the unrestricted integer optimum, even allowing node-by-node asymmetry, lies between `eta_*` and `eta_*+2`. This additive enclosure does not claim exact integer optimality.

### 1.5 Leading constant six remains optimal

Let `D_min=2^(a-u+1)`. In the formal `D_i=infinity` limit, `c_i=0` and the recursion has the explicit solution

`r_i^infinity = (u-i)/6 + 5/18 + (2/9)4^(-(u-i))`,

`R_infinity = u/3 + 2/9 - (2/9)4^(-u)`.

These are the already-known symmetric full-loss solution from the precision-refinement packet.

The new finite recurrence obeys

`R_infinity <= R <= (1-1/(2D_min))^(-u) R_infinity`,

`0 <= C <= ((a+1)/D_min) R`.

For the first inequality, expand the positive backward recursion as a finite sum over increasing index paths. Relative to the limiting recursion, each visited index multiplies its contribution by at most `(1-1/(2D_min))^-1`, and there are at most `u` such visits. The second follows by backward comparison of the two recursions, since every inhomogeneous term `n_i/D_i` is at most `(a+1)/D_min`.

Consequently, if `u->infinity`, `u/D_min->0`, and `(a+1)/D_min=o(M/u)`, while Hermite completeness requires

`W=(M(2L-1)+1)/L=(2+o(1))M`,

then

`eta_*=(6+o(1)) M/u`.

If also `M/u->infinity`, integer rounding changes this by a relative `o(1)`. The thin-gap schedules use `D_min >= (log s)^6` and `a,u=O(log s)`, so they satisfy these conditions.

This proves that the leading constant six is optimal for the stated independent-jet top-cardinal precision certificate even with arbitrary asymmetric multiplicities, including arbitrary omission of nodes among the permitted valuation levels. An improvement from `MD/u` to `o(MD/u)` cannot come from that change alone.

### 1.6 A coarse bound without asymptotic regularity

A simpler inherited scalar argument, combined with symmetrization, gives the following: if `M>=8u` and `sum_t q_t > M(2L-1)`, then some retained node has

`Lambda_t(q) > D_t M/(4u)`.

For the averaged profile, use the already-proved finite normalization-loss lemma to find a level with normalized loss exceeding `M/(4u)`. Since that loss is at most `2q_i`, its multiplicity exceeds `M/(8u)>=1`, making the additional highest-jet evaluation term nonnegative. Symmetrization then transfers the maximum lower bound to the original arbitrary profile.

## 2. Why this does not yet give the requested order improvement

The new theorem resolves one previously identified escape route negatively. It does not prove that cancellation among attainable jets is useless, and does not prevent a different deformation, different mode summation, or recursive representation.

The natural candidate for an order improvement is to encode each exact-weight mode tuple in binary and apply the contraction theorem a second time. Its nominal wire entropy is `O(M/sqrt(u))`, which might suggest another square-root logarithmic saving. The missing interface is real: one group function depends on a linear fraction of these compressed wires at fixed grouping arity, so its degree is linear in the new normalized size, exceeding the required `s^0.9` entry-oracle interface. Turning the group function into a low-degree network is precisely the unsupplied factorization. Rank/unrank algorithms alone do not establish that factorization, and recursive computation of an entry does not split its ports at small wire cost.

Likewise, the original sparse-query reduction retains incidence polynomial degree `O(n)` but binary subset indices use `O(n log log n)` wires. Polynomial degree in incidence variables does not transfer to low degree in index bits: the coefficient table of a single degree-one monomial can be the AND of all index bits. The earlier conditional degree-preserving route already makes this explicit.

Changing the grouping alphabet with depth only changes the available constant capacity in `a=O(log s)`. A root with alphabet `r` obeys a packing condition of the form `r^(2a) s^0.9=o(s)`, so increasing `r` shrinks rather than enlarges the root retained range. Cached exact-weight table contraction changes how the partition entropy is processed, but the existing proofs still have a nonzero root cost on the `M/sqrt(log s)` scale.

No genuine unrestricted logarithmic-order improvement was established in this investigation. The exact asymmetric-node theorem above is a proved new scoped barrier; it should not be presented as a SAT lower bound or a stronger SAT algorithm.

## 3. Executable verification

`research_notes/check_asymmetric_hermite.py` is a standard-library exact-rational checker. It checks:

1. the valuation identity (1) for every leaf;
2. equality of the active-node objective with the convex all-node objective;
3. monotonicity under annular symmetrization;
4. the exact finite minimax candidate's mass and attained objective.

It exhausts all multiplicity vectors on grids of sizes 2, 4, and 8 with multiplicity caps 5, 4, and 2 respectively, and checks 112 rational finite-minimax instances. These are finite error detectors supporting the symbolic proofs, not a formalization.
