# Latest kernel / frontier review (static, 2026-10-27)

## Useful conclusions

1. `sat_adaptive_frontier_2026-10-26` already supplies a **50.30468921410 polynomial-space** normalized-wire time certificate and **31.25239731266 cached time and space** certificate. These beat our iteration-2 `55.3316 / 35.0706` certificates before any new work. The novel ingredients there are adaptive quartet pairing and a six-cost covariance-selected three-block partition, respectively. The former is not merely schedule retuning.
2. `3sat_round3_frontier_20261027` has weaker general-degree coefficients (`63.75735555`, cache `37.93010908 / 33.62304092`) than these and iteration 2. Its stronger-assumption low-degree rows (`23.66616881` polynomial-space, cached `14.23918819 / 12.36130146`) must remain in the portfolio, subject to comparison with other packages.
3. Iteration 2's positive-load sparse scorer is **stronger** than the round3 incremental scorer, not superseded by it. Round3 removes inactive row groups but still scans all candidate labels. Our inherited iteration2 also removes the load-zero baseline, visits only positive cells, and selects the least absent label. Do not re-claim either result as new this iteration.
4. The strongest inherited packet-extraction baseline is **anisotropic** antipodal Gray, not round3's uniform step-two centered Gray. The former needs guard precision `p + v2(prod beta!) + O - 1`, where `O = sum(beta_j : beta_j odd)`, versus round3's `p + v2(prod beta!) + R - 1`. At all-even profiles it uses one bit *less* than forward differences. Round3's cube filter and general common odd-order filter are useful but already known in our inherited source corpus.
5. More importantly, the inherited `subexponential_sat_kernel_improvements` theorem already permits **individual roots of order beta_j+1**, fixes a minimum-exponent coordinate, and uses `G/(1+min beta)` evaluations at precision `p+sum_{j!=k}v2(beta_j+1)`. Any claim that mixed-radix projective extraction is a new identity would be false. Its implementation covers exponents 1 and 2 only. A new implementation for exponents 2 and 4 (roots 3 and 5) remains an honest practical specialization, rather than a mathematical novelty.

## Reviewed files and exact source boundaries

All archive programs were read as data; none was imported, executed, or compiled. Evidence paths below are relative to `eth_iteration3/incoming/`.

- `3sat_round3_frontier_20261027/README.md`, `report/report.tex`, `report/{balancing,packet,cauchy}.tex`; `research_balancing/incremental.py`; `research_practical/packet_extraction.py`; `research_practical_review/extraction_audit.md`.
- `sat_adaptive_frontier_2026-10-26/sat_adaptive_frontier_2026-10-26/report.tex`, `sections/{quartet,joint_objective,degree_flow}.tex`, `audit/independent_mathematical_review.txt`.
- Inherited theorem precision/novelty cross-check: `ETH_Adaptive_Exact_Kernels_2026-10-27/eth_iteration2/sources/late/subexponential_sat_kernel_improvements_2026-10-26/subexponential_sat_kernel_improvements/report.tex`, sections 4–5, especially `thm:antipodal` and `thm:projective`.
- Existing independently authored implementation inspected: `eth_iteration2/code/{sparse_balancing,fused_cauchy}.py` and `eth_iteration2/{sparse_delta_proof,fused_cauchy_new}.md`.

No global independent theorem verification or execution of archived check outputs is claimed.

## Adaptive-quartet theorem details

For six nonnegative undirected edge weights on four blocks, let the complementary pair weights in perfect matching j be `a_j >= b_j`. The best balanced binary pairing has external path weight

`F4 = sum_j(a_j+b_j) - max_j b_j <= sum_j a_j + (2/3)sum_j b_j`.

The squared six-edge norm is `13/3`, or `26/3` over directed singleton edges. The recursive disjoint-support certificate is

`g_r <= sum_j[max(c_j,d_j)+min(c_j,d_j)(1-p_j)^2] + max_a g_(k_a)`.

The source ledger is `g4=26/3, g6=22, g8=110/3, g16=442/3`, and for `r=4^j` it is `26(r^2-1)/45`. Fixed binary has `2(r^2-1)/3`; these powers improve the local coefficient by `sqrt(13/15)`.

The strict schedule is `(r_d)=(16,16,8,6,4,4,...)` and

`eta=(1249/100000, 1249/100000, 26/3125, 107/20000, (27/6400)(5/8)^k)`.

The leading cumulative ranges are `1249/100000,1249/50000,333/10000,773/20000,499/10000`. They meet the root `2 A0 log2 r0 < 1/10` and later `Ad log2 rd < 1/10` packing gates with strict margins. The coefficient is the paid sum `kappa sum f_d sqrt(g_rd)/(r_d sqrt(eta_d))`; the tail ratio is `sqrt(2/5)`. Exact index-cardinality comparisons choose a matching without approximate logarithms. Depth-first evaluation pays every recursive group oracle and retains polynomial space.

Potential optimization: combine this structural evaluator with other new alphabet ledgers/schedules, but do not retain the old fixed-binary norm at these alphabets. Root and tree agents are reviewing stronger certificates elsewhere.

## Joint cached theorem details

For an equal partition into A,B,C, the six costs are three incident construction entropies `I_A,I_B,I_C` and `S-(3/5)H_AB`, `S-(3/5)H_AC`, `S-(3/5)H_BC`. Minimizing their maximum pays *all* directly constructed tables and final rectangular multiplication. Cached group entries still incur paid recursive child calls.

The local recurrence is

`T_d <= poly(s) [2^(alpha_rd K_d) T_(d+1) + 2^(beta_rd K_d)]`,

with `alpha_r=sqrt(2(r-1))/r`, `K_d=kappa M_d/sqrt(u_d)`, `kappa=pi sqrt(2)/ln2`. Joint covariance gives

- `beta9^2=2489356/6638625`,
- `beta12^2=4786024/13540725`.

Source schedule: alphabets `9,12,9,6,4,4,...`, root `A=1/(20 log2 9)`, retained leading ranges `A,1/36-A,1/288,5/864,(1/189)2^-k`. Root local work `31.2523973126509...` dominates descendant-paid totals `30.41173930826,30.23123727305,30.18781782003,30.42570652863`.

The same coefficient is valid space because local maximum costs pay input, output, and workspace tables; ancestor caches add rather than multiply. It is not polynomial space. The coordinate/CRT bridge to field exponent `12/5` is an inherited dependency; no inversion of nonunits in the power-of-two quotient ring is permitted.

## Kernel opportunities and caveats

### Strongest sparse balancing state

After active-row removal, iteration2 scores are

`delta_b = sum_(a active) F'_a (q^w_aj-1)(q^X_ab-1)`.

They preserve all exact dense decisions, first-label ties, conditional scores and final potentials. The work is `sum_j sum_(a active) |positive_support(row a)|`, versus round3's `Q sum_j |active_rows_j|`. Earlier dense input scans, `future[:]` per-column copies, full powers through edge mass, and dense output still impose their own costs. A sparse edge-list API and in-place future updates could improve memory/preprocessing, but need fair same-interface testing; they are engineering opportunities rather than new potential identities.

### Honest projective specialization

For all even beta with entries 2 or 4, choose a minimum beta coordinate k and roots of orders 3 or 5 on the remaining coordinates. The existing projective theorem yields no guard bits and `prod_(j!=k)(beta_j+1)` evaluations. For `(2,2,4,4)`, the counts are 75 mixed-root versus 112 strongest anisotropic-half-grid versus 125 common-order-five. For `(2,4,4,4,4)`, counts are 625 versus 937 versus 625; there is no common-order saving when only the fixed coordinate has exponent 2. Favorable profiles must contain at least two smaller exponents.

The source residue degree `e=4 ceil(log2 s)` contains F16 and hence roots of both orders 3 and 5. Hensel lifting is valid because these orders are odd. Supplied roots must be validated for full orthogonality, not only `root^order=1`; over a general free quotient the latter alone is insufficient. Root preparation/lifting must be shared or charged in benchmarks. No hidden ring enlargement is allowed. Compare at the same quotient ring and immutable creation precision, with equal canonicalization/setup/output charges. Actual wall-clock benefit is empirical, not implied by evaluation counts.

### Existing ratio-fused Cauchy implementation

Retain iteration2's unit-ratio cache and absorbed target prefactor: complete-table multiplication count `N^2+N` versus matched one-inversion quadratic baseline `(5N^2+N)/2`. This is inherited work now. Ordinary mode truncation below precision is also inherited and does not improve the SAT order. A practical early-zero target-table optimization may be possible using the monotone `a+1-i+4q-2 popcount(q)` lower bound, but a complete source-table API cannot discard source values merely because matching target rows vanish. Intermediate zero residues can later recover after normalization; never terminate a source recurrence based only on a displayed zero.

## Scope that must remain explicit

Every coefficient multiplies `s/sqrt(ceil(log2 s))` on normalized Boolean-wire size, not n directly. All arguments import the upstream exact deformation, recovery, integrality, child factorization and immutable creation-precision interfaces. They preserve the density envelope

`poly_k(n,m) 2^O_k( n/sqrt(log n) * min(log(2+m/n),log log n) )`.

Neither this static review nor the source degree-flow identity supplies the missing compiler preserving low degree, compressed mode multiplicity, bounded local graph degree, short immutable descriptions, and affordable recursive entry evaluation. Degree flow is a true algebraic invariant; it is not enough for a smaller logarithmic order. Conditional targets and unquantified constants in the alternate manuscript must not be claimed dominated.

## Closing implementation result

The mixed3/5 opportunity above is now implemented and independently checked in `code/mixed_projective.py`, with a strong anisotropic Gray baseline, common-root comparator, coefficient-DP checks and an affine entry adapter. `mixed_projective_proof.md` and `mixed_projective_section.tex` are the final explanation/report input. Final root setup uses classical precision-doubling Newton (credited as standard), with the bitwise method retained as an oracle; this cuts lifting rounds from p−1 to ceil(log2 p).

The final five-repeat ledger `results/mixed_projective_benchmark.json` anchors source/script SHA-256 and includes **root construction inside both fresh-filter calls**. Six selected mixed-even profiles yield fresh-root inclusive ratios 1.34–4.67 versus common-root filtering and 1.005–1.68 versus strongest inherited anisotropic half-grid; the first is effectively tied. The eight-ones negative case is about 24 times slower with mixed odd filtering. Historical bitwise-run regressions are retained. These are synthetic component measurements, not complete SAT evidence. No new mixed-character identity is claimed.
