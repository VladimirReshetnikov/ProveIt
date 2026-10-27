# Sparse positive-support scoring for factored matching potentials

## New composition and scope

The preceding iteration-3 factorization already reduced the incoming matching kernel's update work from O(MQ²+VQ) to O(MQ+VQ). We can further combine that factorization with the **previously supplied positive-support delta technique**. The new contribution is its exact application to both phases of this matching potential, not a claim to invent sparse conditional expectations or the delta identity.

The original routine processes all left vertices before all right vertices. Preserve that order, first-fit matching partition, exact thresholds, label-index tie break and every selected potential. Let K be the number of matchings, M the number of edge occurrences, Q labels and V incident vertices. Define

`d=1+1/(ηQ²)`, `c=1+1/(ηQ)`, `t=1+1/η`.

The exact table for matching j factors as

`P_jab=s_j x_ja B_jab`,

where `s_j=t^(-h_j)d^(U_j)`, `x_ja=c^(L_ja)` and `B_jab=t^(C_jab)`; U counts edges with both endpoints unassigned, L counts edges with assigned-left label a and free right endpoint, and C counts completed label pairs. Both x and B have default value one. Unlike the array-factorized implementation, the sparse implementation needs no full row-sum arrays.

## Candidate delta: left phase

When a left vertex is processed, its opposite endpoints are all free. For each incident matching replace s by s'=s/d. Since no right vertex has been processed, B is identically one. Candidate a has a candidate-dependent contribution

`sum_incident j s'_j(c−1)Q x_ja`.

Subtract its candidate-independent unit baseline and define

`δ_a=sum_incident j [s'_j(c−1)Q](x_ja−1)`.

Only stored x entries differ from one. Their values exceed one, so δ≥0. After choosing a, update x_ja←c x_ja for each incident matching.

## Candidate delta: right phase

All left endpoints are already assigned. For an incident edge whose left endpoint has label a, first replace x_ja by x'_ja=x_ja/c. The true remaining count cannot be negative, hence x'_ja≥1; delete the dictionary entry if it becomes one. Candidate b has candidate-dependent term

`sum_incident (j,a) s_j x'_ja(t−1)B_jab`.

Subtract the unit baseline and set

`δ_b=sum_incident (j,a) [s_j x'_ja(t−1)](B_jab−1)`.

Iterate only stored entries in that B row. Again every delta term is nonnegative. After choosing b, update B_jab←t B_jab.

## Exact selection and full selected trace

For either phase, all candidate potentials have a common base plus δ_label. Conditional averaging therefore gives exactly

`Phi_candidate = Phi_current + δ_candidate − (sum_label δ_label)/Q`.

If fewer than Q labels have positive delta, choose the **least absent label**: its delta is zero, smaller than every stored positive delta. Otherwise choose the minimum `(δ_label,label)` lexicographically. The selected potential is obtained directly from the displayed identity. This proves equality of labels, ties and the full selected trace by induction, not merely equality of final loads. No floating-point comparisons occur.

The ordinary output interface requests only the selected trace. If an optional test/diagnostic requests every candidate, constructing those values still costs O(VQ) output work, and the implementation pays it. The sparse benchmark does not silently omit any requested output: all three methods return identical assignment, load matrix, matching partition, threshold data, initial/final potential and selected trace.

At completion all x dictionaries must be empty. The final exact potential is independently reconstructed as

`sum_j s_j [Q² + sum_(stored a,b)(B_jab−1)]`.

This is an O(K+M)-state check; it is not a full Q² materialization.

## Work, storage and bit costs

Let X_j(v) be the number of nondefault x entries in incident matching j at a left-vertex step v, and C_ja(v) the number of nondefault cells in its relevant B row at a right-vertex step. Scoring work is

`O(M+V + sum_left v sum_incident j X_j(v) + sum_right v sum_incident(j,a) C_ja(v))`.

Choosing the least missing label takes at most the number of touched scores plus one probes; choosing a fully touched minimum scans those scores. Hence it does not introduce an unconditional Q scan. Each support count is at most Q, so the bound is at most O(MQ+VQ), while sparse instances can be strictly cheaper. This is a support-sensitive refinement, not a smaller worst-case Q order than the array-factorized method.

At most M nondefault x cells and M nondefault B cells can exist: each is witnessed by an assigned-left or completed edge in its matching. Transient scores are bounded by the touched support. Potential-state storage is therefore **O(K+M) rational values**. Graph, assignment and selected trace are separately present; the unchanged returned dense load matrix still costs Θ(Q²) cells and writes. That output cost is not hidden by the sparse-state claim.

Initial powers, first-fit coloring O(MK), vertex sorting, rational normalization and polynomial integer bit lengths remain charged exactly as before. Rational denominators and bit lengths retain the matching-product scale O((h_max+m_max)log(ηQ+2)), with logarithmic sum overhead; arithmetic operations are not unit-cost large-integer instructions. The formulas rely on the all-left/all-right order, not arbitrary interleavings.

## Evidence

`tree_checks/matching_factorized.py` now exposes `method='sparse'` in addition to the unchanged strengthened `dense` and array-`factorized` methods. Tests compare all four methods including the literal product oracle on full candidate values, plus larger cases against both maintained references. All code is authored in this iteration; no archive program is imported or executed.

`tree_checks/benchmark_matching_factorized.py` runs all three maintained methods on the same stored graphs, with five alternating/rotating repetitions after equal-output warmup. Full initialization, output and each method's invariant checks are charged. Sparse averaging is deliberately symbolic; full unrequested candidate vectors are not materialized. The array-factorized method is the primary stronger comparator for the added sparse step. Final timing results are below; independent audit status is recorded separately in the QA artifacts. The prior exact source/benchmark pair is retained as `matching_factorized_before_sparse.py` and `matching_factorized_before_sparse_benchmarks.json`; those are historical ablations, not current headlines.


## Final bounded three-method benchmark

Source and benchmark are frozen. Implementation SHA-256 is `c138447377443691f0266c5999d2c2b359a4281d4bdac2f3106310571298be05`; benchmark SHA-256 is `d45758f0d3bb01883d745ad43d15996fbbd14d06e634f07d7e1f764305d30182`. Both were captured before timing and asserted unchanged at the end. The ledger contains all11 fixtures, raw five-repetition wall/CPU samples, graph edges, medians, positive-output-cell counts and exact-output validation.

The primary comparison for this added sparse step is the **array-factorized method**, not the weaker dense table:

| Fixture | Q | Array-factorized / sparse wall | Array-factorized / sparse CPU |
|---|---:|---:|---:|
| tiny | 1 | 1.383× | 1.386× |
| tiny-q2 | 2 | 1.532× | 1.530× |
| random-M16-Q2 | 2 | 1.914× | 1.913× |
| random-M32-Q4 | 4 | 2.065× | 2.065× |
| random-M64-Q8 | 8 | 3.457× | 3.456× |
| random-M96-Q12 | 12 | 3.433× | 3.432× |
| random-M128-Q16 | 16 | 3.866× | 3.865× |
| random-M192-Q24 | 24 | 3.777× | 3.776× |
| parallel-M96-Q12 | 12 | 4.792× | 4.788× |
| single-matching-M96-Q12 | 12 | 2.044× | 2.044× |
| filled-single-matching-M256-Q8 | 8 | 1.576× | 1.503× |

The filled control has one matching,256 edges,512 vertices and all64 Q² cells positive; an explicit assertion verifies this. Its1.576× wall /1.503× CPU gain demonstrates that this test did not rely on an unfilled final table. Nevertheless, all timings are synthetic component measurements in a shared executor, not a universal speedup claim or SAT runtime evidence. No claim is made that every dense-support regime benefits. The strongest observed random-fixture factorized/sparse ratios are1.91–3.87×, not the larger ratios against the older dense implementation.

The final ledger also retains every D/F comparison and its regressions (approximately0.965× on tinyQ1 and0.936× on M16,Q2). No sparse regression occurred in this bounded set; this is an observation, not an extrapolation. The ordinary interface returns the full **selected potential trace**, not all candidate potentials; all-candidate equality is tested separately and its optional materialization remains charged.

The normal and `-O` primary suites agree on696 four-method oracle comparisons plus32 larger cases. They compare all6,000 candidate values and2,400 selected trace values in the small cases; the final filled benchmark adds its separate exact-output equality control. Earlier pre-sparse ledgers remain explicitly historical rather than mixed into these final medians.

## Final independent audit outcome

The final independent audit **passed**, including source/script hashes, every stored median and ratio, all11 fixture counts and normal/`-O` primary replays. A separate complete-labeling oracle gives2,232 maintained-method candidate-value equalities. The saturated M=256,Q=8 observer reconstructs every U/L/C state and potential across all512 vertices, checks440 full-support and72 absent-support choices, verifies exact x deletion, and confirms all64 cells finish at load4. The audit found no blocker in the positive-support algebra, selected-trace identity or O(K+M) potential-state proof. Evidence is in `qa/audit_iteration3.md` and its independent JSON receipts.
