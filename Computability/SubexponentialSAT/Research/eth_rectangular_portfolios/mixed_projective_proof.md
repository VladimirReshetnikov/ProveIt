# Mixed 3/5 projective implementation: proof, credit and measured scope

## Result and novelty boundary

The new deliverable is a working exact **implementation specialization**, not a new coefficient identity. The inherited `subexponential_sat_kernel_improvements` report already proves a projective formula with individual orders `d_j=beta_j+1`; its program handles target exponents one and two. The newer `3sat_round3_frontier` program supports a **single** common odd order and dispatches only cube roots. We add a mixed-order 3/5 Gray kernel for profiles containing exponents two and four, using one fixed rank-four quotient ring. It composes with the unchanged packet-entry interface and leaves every global SAT exponential-order/certificate bound unchanged.

All reviewed archive programs were inspected as data only. The implementation, baseline and checks in `code/mixed_projective.py`, `code/check_mixed_projective.py`, and `code/benchmark_mixed_projective.py` were authored for this iteration and import no archive module. The earlier general theorem receives credit explicitly. The grep ledger `results/mixed_root_novelty_grep.txt` records source-text matches; absence of an implementation in this inspected corpus is not a global priority claim.

## Exact mixed-character formula

Let `H(Z)=prod_(r=1)^R sum_j a_rj Z_j` be homogeneous, with nonnegative target beta and `sum beta=R`. Coordinates with beta zero can first be set to zero and dropped; the empty product is handled as one. For positive remaining targets fix a minimum-target coordinate `k` to one. For each free coordinate choose an available odd order `q_j > beta_j` and `q_j > beta_k`, with orthogonal character root `omega_j`. Then

`[Z^beta]H = (prod_(j!=k) q_j)^(-1) sum_(0<=g_j<q_j) prod_(j!=k) omega_j^(-beta_j*g_j) H(1,(omega_j^g_j)_(j!=k))`.

The inverse is only of an odd scalar. Orthogonality retains a monomial alpha precisely when `alpha_j=beta_j+q_j m_j` on every free coordinate, with `m_j>=0` because `0<=beta_j<q_j`. Homogeneity gives `alpha_k=beta_k-sum q_j m_j`; any positive m forces alpha_k negative. Thus only alpha=beta remains. This proof also permits a zero-target fixed coordinate if it is deliberately retained, but dropping zero-target coordinates generally gives a smaller grid.

For targets in `{2,4}`, choose orders 3 and 5 and fix a target-two coordinate when one exists. The count is exactly `G/(1+min beta)`, with `G=prod(beta_j+1)`, and no guard bits. This is a direct case of the inherited theorem. More generally, our implementation accepts targets 1 through 4 and chooses the smallest of {3,5} strictly exceeding each target; odd-target cases are valid but can be much worse than inherited sign/antipodal methods and are not advertised as a new best branch.

### Why a minimum-target pivot suffices for available-order filtering

Let `m(b)` be the smallest available odd order exceeding b. If pivot k has target b_k, admissibility requires free order `m(max(b_j,b_k))`. Suppose b_i<=b_k. Swapping pivot k for i changes the factor for i, formerly `m(b_k)`, to the factor for k, again `m(b_k)`, while every other factor weakly decreases. Thus a minimum-target pivot minimizes this product among pivots for this order-selection rule. This is a simple implementation-selection argument, not a novel projective identity.

## One existing quotient, no free enlargement

The prototype works in `(Z/2^p Z)[U,V]/(U^4+U+1,V^ell)`, a free module of rank `4 ell`. Modulo two, the quartic has no linear factor; its remainder modulo the only irreducible quadratic `U^2+U+1` is one. Hence it defines F16. The explicit residue U has order fifteen: the program checks powers fifteen, three and five before lifting.

The default root routine uses **classical precision-doubling Newton lifting**, not a new identity. If `x^15=1+e` modulo the target precision, with `e` divisible by `2^k`, set `x' = x-x*e/15` modulo `2^min(2k,p)`. The binomial expansion gives `(x')^15=(1+e)(1-e/15)^15=1+O(e^2)`. Only the odd scalar 15 is inverted, and the argument remains valid with nilpotents. The program checks the root and preservation of all prior bits after every lift. It takes `ceil(log2 p)` lifting rounds instead of the earlier bitwise routine's `p-1`; that independently structured bitwise routine remains as a regression oracle. Powers `rho^5` and `rho^3` supply orders three and five; all their orthogonality sums are checked explicitly rather than inferred from multiplicative order in an arbitrary ring.

For the source interface, the original residue degree is `e=4 ceil(log2 s)`, so its field already contains the unique F16 subfield and both orders. A root must be found/represented inside that original ring and lifted; no additional ring dimension is silently allocated. The present fixed rank-four implementation is a local component prototype, not an implementation of arbitrary source-ring embeddings or a complete SAT solver. Timings compare all methods in exactly the same quotient ring and nilpotent dimension. They charge new root lifting separately in the `mixed_fresh_lift` variant; cached-root runs exclude only that previously paid lift, not root validation.

## Gray arithmetic and space

All roots come from one primitive fifteenth root rho. A free coordinate with order q uses `rho^((15/q)g)`, and the total character is a lookup of `rho^phase` with `phase=-sum beta_j(15/q_j)g_j mod15`. Reflected mixed-radix Gray traversal changes only one g by plus or minus one. Precomputed neighboring-root increments update all R current row sums in O(R) additions; phase updates use integer arithmetic and one lookup. Each point uses R product multiplications and one character multiplication.

For `P=prod_(j!=k)q_j`, work is `O(R P + R sum_j q_j + 15)` ring operations plus polynomial integer/input work. Storage is `O(R sum_j q_j + R+t)` ring elements; there is no grid-indexed table. Coefficients are canonicalized at immutable creation precision p before evaluation and the final result is returned at p. No even inverse or post-reduction nonunit division occurs. For profiles `{2,4}`, P is never larger than the strongest inherited antipodal count and is asymptotically 2/3 of it when min beta=2, or 2/5 when all beta=4; common order-five can be exponentially larger in the number of free target-two coordinates. These are packet-entry operation counts, not new SAT exponent bounds.

## Strong matched baselines

The common-root comparator uses the same primitive root, root checks, Gray traversal, row-sum updates, canonicalization and ring arithmetic, but chooses one order 3 or 5 for every free coordinate. The centered baseline is **anisotropic antipodal Gray** with step one for even targets and step two for odd targets. Its guard bits are `v2(prod beta!)+sum_(beta_j odd)beta_j-1`, not the weaker uniform step-two loss `v2(prod beta!)+R-1`. The selected all-even profiles therefore compare against the stronger inherited baseline.

The adaptive function in this module chooses only among its mixed-odd and anisotropic candidates by evaluation counts. It is a demonstration dispatcher, **not** a claim to supersede the existing `{1,2}` sign/cube dispatcher or all possible packet kernels. Counts do not guarantee minimum wall time; production use must retain the inherited portfolio and calibrate on actual generated packet profiles.

## Exact checks

Both normal Python and `python -O` pass:

- 1,880 exact output equalities against an independently structured coefficient DP, including exhaustive 4-by-2 binary matrices, random signed/noncanonical quotient entries, precisions 1/3/13, nilpotent lengths 1/2, zero targets, singleton targets and mixed odd targets.
- 96 affine-adapter equalities, including zero constant target and requested degree exceeding the number of affine factors.
- 83,696 independent monomial alias checks for targets of length two through four and exponents one through four.
- 125 Gray-grid coverage/one-coordinate-step checks.
- 12 primitive-root lifting fixtures over six precisions and two nilpotent lengths, each comparing precision doubling against the preserved bitwise oracle.
- Seven invalid-root/input rejection controls, plus an inadequate-order/nonminimal-pivot alias counterexample.

These finite checks are not a formal proof or a run of the upstream SAT counter. Test outputs are retained under `results/mixed_projective_checks*.json`.

## Five-repetition synthetic component measurements (final doubling-root version)

Python 3.12.14 on the shared Linux executor; fixed seed 271028; one warmup per method; five rotated/reversed timing repetitions. Generation and the direct correctness oracle are excluded; canonicalization, root validation, polynomial increment setup, extraction, and output are timed. **Both fresh-root methods also construct the root inside every timed call**, using the same precision-doubling routine. Raw wall/CPU samples, source/script hashes, environment and case parameters are retained in `results/mixed_projective_benchmark.json`. Each run is checked against the exact oracle.

| beta | p / ell | Common points | Half points | Mixed points | Fresh common / fresh mixed | Half / fresh mixed |
|---|---:|---:|---:|---:|---:|---:|
| 2,2,4,4 | 32 / 1 | 125 | 112 | 75 | 1.847 | 1.005 |
| 2,2,2,4,4 | 64 / 1 | 625 | 337 | 225 | 2.421 | 1.531 |
| 2,2,2,2,4,4 | 128 / 1 | 3125 | 1012 | 675 | 4.672 | 1.386 |
| 2,2,4,4,4 | 32 / 1 | 625 | 562 | 375 | 1.662 | 1.560 |
| 2,2,4,4 | 32 / 2 | 125 | 112 | 75 | 1.591 | 1.102 |
| 1,1,1,1,1,1,1,1 | 32 / 1 | 2187 | 128 | 2187 | 1.162 | 0.042 |
| 4,4,4 | 32 / 1 | 25 | 62 | 25 | 1.054 | 1.728 |
| 2,2,4,4 | 1 / 1 | 125 | 112 | 75 | 1.338 | 1.677 |

Across the six selected mixed-even fixtures, **fresh-root inclusive** median ratios are 1.34–4.67x versus fresh common-root filtering and 1.005–1.68x versus anisotropic half-grid extraction. The first fixture is effectively a tie in these noisy measurements. With roots already cached, the corresponding ranges are 1.54–6.26x and 1.27–2.29x. These are selected, nonrepresentative synthetic components; the larger timing ratios are not inferred from evaluation counts.

The eight-ones adversarial profile makes mixed odd filtering about **23x slower with a cached root and 24x slower with a fresh root**, and the dispatcher takes the half-grid. Equal-count all-four variants have no mixed-radix structural advantage. The fresh-lift median can be smaller than its cached-root median on a shared executor; that is measurement variation, not negative setup cost. Count-only dispatch also has measured overhead and does not universally beat its selected kernel or every baseline.

Earlier bitwise-root runs are preserved as `mixed_projective_benchmark_initial.json` and `mixed_projective_benchmark_bitwise_final.json`. The latter included a 3.4% half-grid regression on a nilpotent case and fresh-root losses. They are historical evidence of the earlier implementation and shared-host timing variability, not the final default's reported table. The final benchmark is explicitly tied to its source and script SHA-256 hashes. No further reruns were selected to remove unfavorable cases.

No complete-SAT speedup, practical crossover theorem, statistical significance or universal wall-clock dominance is claimed. The robust implementation-level conclusions are exact equality, the stated evaluation counts, polynomial streaming state, and logarithmically many root-lifting rounds; wall time remains workload- and environment-sensitive.
