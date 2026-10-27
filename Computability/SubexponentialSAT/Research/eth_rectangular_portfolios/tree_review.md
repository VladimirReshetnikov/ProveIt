# Static review of adaptive schedules, tree certificates, and bounds

Scope: `eth_adaptive_schedules_2026-10-26`, `sat_adaptive_tree_certificate_2026-10-26`, `sat_adaptive_bounds_2026-10-26`, from iteration-3 pinned intake. Archive TeX, README, implementation source and stored receipts were read as data; **no archive program was executed**. Newly written checks are under `tree_checks/`.

## Findings delivered immediately

| Branch | Strongest assigned-packet certificate | Space/premise |
|---|---:|---|
| Generic streamed | 46.184845586731 | Polynomial; root degree ≤ceil(s^0.9) |
| Generic cached | 30.891018920366 | Space 30.753912832055; same generic degree |
| Very-low-degree cached | 13.379649066270 | Space 13.253024933008; root degree ≤ceil(s^(1/12)) |

All numbers in the source table multiply E(s)=s/sqrt(log2 s) in a base-two exponential bound, and s is normalized Boolean wires, **not SAT variables**. The old iteration-2 55.331622 / 35.070614 comparisons are obsolete. All results retain exact deformation/recovery, source/target-local full slope-four modes, nearly lossless asymmetric packing, exact list indexing, paid recursive child entries and immutable creation precision. Cached branches additionally use the integer-coordinate/CRT fast-matrix bridge. No smaller logarithmic order or full SAT implementation was found.

### New polynomial-space composition

Combine the adaptive binary-flag local constant

`b_r²=(r-1)(4r+10)/(9r²)` for r=4,8,16

from `sat_adaptive_bounds/.../report/flags.tex` with the stronger multistage schedule in `subsat_rectangular/.../sections/polyspace.tex`, retaining the latter's ordinary fixed separators at r=6,5:

- r=(16,16,8,6,5), f=(12499/10^6,12499/10^6,2083/250000,107/20000,219/50000).
- Masses m=(1,1/8,1/64,1/256,1/768), then m5=1/1920.
- r=4 tail, f_(5+j)=(513/200000)(5/8)^j; use adaptive flags there too.
- Local coefficients at r=6,5 remain sqrt(24)/6 and sqrt(18)/5.

The fully paid streamed sum is

`C=κ[ Σ_(i=0)^4 m_i b_(r_i)/sqrt(f_i) + m5 b4/(sqrt(f5)(1-(1/2)/sqrt(5/8))) ]`

where κ=πsqrt(2)/ln2. It equals **46.07107819584879...**, with safe eventual coefficient **46.072**. This improves the updated 46.184845586731 certificate, not merely the stale old bound. This is a compatible new composition, not a new flag lemma, schedule identity, or change of asymptotic order. All packing/degree/precision/depth gates are unchanged from the strict rational schedule; replacing only the paid separator coefficient cannot invalidate them. Independent rational arithmetic (Machin π, positive ln2 series and integer square-root enclosures) passed normally and under `-O`; see `tree_checks/schedule_combinations.json`.

### New low-degree rectangular-tree composition

Use the matrix-review agent's final four-plan r=13 rectangular coefficient (the three inherited plans plus the explicit fourth plan in `four_plan_portfolio_new.md`)

`β13²=27980397750833/82810000000000`, `α13=√24/13`.

For root degree ≤ceil(s^(1/12)), choose fixed r=13 at all active depths, A=119/1000, q=24/125, and

`u_d=floor[A(1-q) λ q^d]`, `a_d=Σ_(i≤d)u_i+(d+1)b`, `b=ceil(6log2 λ)`, `λ=ceil(log2 s)`.

Stop at H=ceil(s/λ^(2/3)). The total leading taper is A. All retained and newly generated degrees are ≤s^(A+o(1)), because 1/12<A. Every packing gate is dominated by A(1+2log2 13)<1; the exact certificate is **338^119<2^1000**. For a hypothetical active path of depth (2/3)log_6 λ+O(1), minimum taper is λ^[1+(2/3)ln(q)/ln6+o(1)], which diverges since q>1/6. Nearly lossless packing gives child ratio 2/13+o(1)<1/6, closing the bootstrap. Buffers, inherited precision, immutable entries and leaf costs are handled exactly as in the incoming low-degree theorem, with larger margins.

On the E(s) scale, local K terms have initial coefficient `K0=κ/sqrt(A(1-q))` and ratio `γ=(2/13)/sqrt(q)`. The complete recurrence is

`T_d ≤poly(s)[2^(α13 K_d) T_(d+1)+2^(β13 K_d)]`.

Its coefficient is `K0 max{β13,α13/(1-γ)}`. The exact rational enclosure proves the first term strictly dominates (the whole paid child series has coefficient12.004596197276...), so

**C_time=C_space=12.015609290141210... <12.016**.

Ancestor tables add in storage; their exponents do not multiply. This improves the updated low-degree 13.379649/13.253025 certificate and our prior three-plan12.123986736154237 composition under the **same stronger premise**, and is not a generic-degree bound. The storage claim uses the new rectangular bridge's max-input/output bound plus the tree certificate's chosen-operation cost domination. `tree_checks/check_schedule_combinations.py` checks exact capacities, paid infinite tail and five negative controls; normal/optimized JSON agree. The four-plan rectangular support certificate is also independently audited by `tree_checks/audit_four_plan.py`, which reconstructs operation sets by bit masks and exhaustively checks the73,298,242 support quadruples in a different enumeration order; primary evidence remains in `matrix_checks/`. The prior three-plan result used q=181/1000; lowering only its local coefficient without retuning q would leave a dominant paid child series, so the final change to24/125 is necessary for this clean bound.

### New degree-s^(0.51) polynomial-space composition

The same flags improve the useful intermediate-degree branch, not only the generic case. Under root degree ≤ceil(s^(51/100)), replace the iteration-2 low-degree prefix's two r=15 levels by r=16 levels with cumulative tapers A0=1531/25000=.06124 and A1=1111/10000=.1111. Continue with the old arities/cumulative fractions:

| d | r_d | A_d | f_d=A_d−A_(d−1) |
|---:|---:|---:|---:|
|0|16|1531/25000|1531/25000|
|1|16|1111/10000|2493/50000|
|2|8|357/2500|317/10000|
|3|6|81/500|12/625|
|4|5|1771/10000|151/10000|
|5|4|1911/10000|7/500|
|6|4|1999/10000|11/1250|

For d=7+j, r=3 and f_d=(391/40000)(3/4)^j. The total taper is 239/1000 and the leading wire mass at depth7 is **1/7680**. Use adaptive flags at16,8,4 and ordinary fixed balanced separators at6,5,3. Let m0=1 and m_(d+1)=2m_d/r_d. Then the fully paid coefficient is

`C_.51=κ[Σ_(d=0)^6 m_d b_(r_d)/√f_d + (1/7680)(√6/3)/(√(391/40000)(1−(2/3)/√(3/4)))]`

= **21.139416167998583... <21.14**.

The root degree gate is exactly .51+8(.06124)=.99992<1. Depth-one rounding has 9(.1111)=.9999<1. Subsequent old-degree and rounding gates are `(51/100)+A_d log2 r_d<1` and `A_d(1+2log2 r_d)<1`; using exact 6^200<2^517, 5^500<2^1161, 3^200<2^317 verifies all of them with fixed gaps. Since A_(d−1)≤A_d, fresh-side `2A_d log2 r_d+A_(d−1)<1` follows from rounding. All newly created degrees have exponent≤.239<.51. Keep b=ceil(6log2 λ), u_d=floor(f_d λ), a_d=Σu+(d+1)b and H=ceil(s/λ). The original precision argument is unchanged.

For completeness, hypothesize active paths through log_(10/7) λ+O(1). The tail minimum taper is λ^[1+ln(3/4)/ln(10/7)+o(1)], which diverges because3/4>7/10. Packing gives true child ratio2/3+o(1)<7/10, validating the depth bound. Padding loss products over O(log λ) levels are1+o(1). Leaves, original entry costs, new packet entry work exp(s^(.239+o(1))) and per-level polynomial work are lower order after paid path costs. Depth-first operation remains polynomial space.

The new bound improves the matching **degree≤s^.51** iteration-2 certificate25.163765415229 and also dominates the older narrower degree≤s^(1/12) polynomial-space23.666168807146 certificate, although it does not replace faster extra-memory low-degree branches. It is a new compatible flag/schedule composition, not a smaller logarithmic order or an automatic numeric SAT-variable bound. The exact checker now records this certificate and five negative controls; normal/`-O` outputs agree.

## Mathematical static audit

- The linear-flag proof is internally consistent: a path support includes pairs `(a,a+d)` exactly when `a∈x+V_(k-1)` for the unique flag layer containing nonzero d. Affine-subspace intersection size is bounded by the corresponding homogeneous intersection; averaging maximizing leaves then gives the claimed norm. The claim of local optimality is correctly restricted to balanced binary trees and the Euclidean entropy relaxation.
- Tree support averaging does not exchange min/max or assume arbitrary edge-coordinate permutations: `min_j F_j ≤mean_j F_j`, then enumerate the fixed finite support tuples. Q9=3304 and Q13=7074 are supplied finite certificates, not independent replays here. The exact selector uses integer products of list cardinalities.
- Every cached singleton factor is paid through α_r=√(2(r-1))/r. The tail maxima in the 9→13→7 schedule explicitly include all child-call prefixes, not just root matrix cost.
- The selected tree's storage is bounded by its actual work because every table is an input/output of one operation. Root old size-only bound 2/3 would not justify the stated 30.753913 storage; the new selected-cost argument is necessary and is present.
- The table-width lower bound `2ceil(r/3)(r-ceil(r/3))` concerns explicit full boundary tables on complete pair graphs, not SAT or implicit/cancellation-based representations. Equal-inventory exact-budget examples are feasible in the stated abstract mode inventory, not evidence that every actual SAT tensor realizes the extremal nonzero factors.
- No blocking error was found in these new finite lemmas by static review. This is not an independent verification of the whole upstream ETH manuscript or a formal proof.

## Already supplied practical improvements; do not reclaim

`eth_adaptive_schedules` already supplies exact matching-product increments, update work O(MQ²+VQ) versus full recomputation O(VMQ³), with O(KQ²) rational table storage, and common-denominator integer column scoring of already-known dense O(NQ²) order. Shipped synthetic matching speedups 5.7–132.8x are against a much weaker recomputation reference, not the strongest new factorized implementation. Integer column speedups 3.9–10.9x are synthetic component results. The previous iteration's sparse positive-support scoring and fused Cauchy transitions remain credited prior work.

The schedules report explicitly proposes shared-denominator matching updates as future work. It does **not** contain the separable row-factor representation derived below.

## New matching-factorization refinement

For a fixed matching j, all left vertices are processed before all right vertices, exactly matching incoming sorted `('L',u),('R',v)` order. Let η be the reference concentration parameter, Q labels, and

`d=1+1/(ηQ²)`, `c=1+1/(ηQ)`, `t=1+1/η`.

Write U_j for edges with neither endpoint assigned; L_ja for edges whose assigned left endpoint has label a and whose right endpoint remains free; C_jab for completed edges of pair labels (a,b). Then the incoming exact potential table factors as

`P_jab = s_j x_ja B_jab`, `s_j=t^(-h_j)d^(U_j)`, `x_ja=c^(L_ja)`, `B_jab=t^(C_jab)`.

Maintain `R_ja=Σ_b B_jab`, `S_j=Σ_a x_ja R_ja`; the full potential is `Σ_j s_j S_j`. Initially B is all ones, represented by an empty dictionary, R=Q, x=1, S=Q². B acquires at most one new nondefault cell per completed edge, so **working potential-state storage**, excluding graph, trace and the returned dense Q×Q load matrix, is O(KQ+min(M,KQ²)) rational values, not an obligatory dense KQ² table. Producing the unchanged dense load output still costs Θ(Q²) cells and writes. Initialization includes O(KQ) state writes plus separately charged binary powers.

For a left vertex, each incident matching's edge has unassigned right endpoint. Replace s by s/d and add candidate correction `(s/d)(c-1)x_a R_a`. Common base changes by `(s/d-s)S`. After choosing a, multiply x_a by c and update S in O(1).

For a right vertex with already-labeled left neighbor a, first replace x_a by x_a/c. The common potential change is `s(x_a/c-x_a)R_a`. Candidate b adds `s(x_a/c)(t-1)B_ab`. After choosing b, multiply B_ab by t and update R_a and S in O(1).

Each edge is incident to at most one occurrence per matching per vertex, so all Q candidate corrections cost O(Q) per edge endpoint. Total update work is **O(MQ+VQ)** rational operations, with O(1) state updates per incident edge after a choice. Exact averaging and smallest-label tie handling are unchanged. Initial powers, first-fit matching coloring O(MK), input sorting O(Vlog V), and rational bit complexity remain separately charged. Denominator/bit growth is no worse in scale than the original matching conditional products; no constant-time-big-integer assumption is made.

Author-written implementation and literal conditional-expectation oracle are `tree_checks/matching_factorized.py`; an independently structured maintained dense baseline provides a fair performance comparator. No archive code is imported/executed. Test/benchmark outcome will be appended after completion.

### Matching validation status

The normal run passed **696** exact three-way comparisons against a literal conditional-product oracle and the authored maintained-dense reference, plus **32** larger dense/factorized comparisons. It checked **2,400** selected trace values and **6,000** candidate values (counts from oracle cases), including Q=1, empty graphs, parallel edges, ties and η=1. Normal and `-O` receipts are identical; see `tree_checks/matching_factorized_checks{,_optimized}.json`.


### Array-factorization ablation benchmark

The **strengthened baseline caches each dense row sum**, rather than recomputing old/new sums from all row cells. It still updates the explicit dense conditional-product table and costs O(MQ²+VQ). Both implementations include first-fit coloring, exact initialization, all candidate-averaging checks, selected trace, dense load output and final invariant checks. Five alternating repetitions follow equal-output warmup. This pre-sparse ablation is preserved with its matching source as `tree_checks/matching_factorized_before_sparse_benchmarks.json` and `matching_factorized_before_sparse.py`. The final three-method ledger is described below.

| Fixture | Q | Median wall speedup dense/factorized |
|---|---:|---:|
| 16 random edges | 2 | 1.19× |
| 32 random edges | 4 | 1.62× |
| 64 random edges | 8 | 2.03× |
| 96 random edges | 12 | 2.44× |
| 128 random edges | 16 | 4.05× |
| 192 random edges | 24 | 5.17× |
| 96 parallel edges | 12 | 7.53× |
| 96-edge single matching | 12 | 2.16× |

**Regression retained:** one-edge Q=1 gives0.868×; one-edge Q=2 gives1.231×. Tiny timings are noisy and no universal speedup is claimed. Random-fixture CPU ratios are1.19–5.17×; all final sample medians are in the ledger. These are synthetic exact packing-component results in a shared executor, not end-to-end SAT timings or a formal performance lower bound. A production dispatcher may retain the dense routine for tiny cases, but no benchmark is presented as if such an untested policy were already implemented.

The earlier provisional measurements used a less-optimized row-sum baseline and are **superseded**, not retained as headline gains. An independent audit passed the final source normally and under `-O`, using a separate exhaustive-completion oracle (2,400 labelings,126 instances,744 conditional candidates) rather than the product-form oracle; it also verified benchmark hashes/medians and the paid resource scope. See the iteration-3 audit artifacts.


## Final sparse matching extension

The parent identified a further compatible composition with the previous positive-support delta scorer. Full proof is `sparse_matching_new.md`; this is the final matching method, while array factorization and row-sum-cached dense products remain fair comparison branches.

For the left phase, set s'=s/d and accumulate only stored positive terms `δ_a=Σ s'(c−1)Q(x_a−1)`. For the right phase, first replace x_a by x_a/c (delete the entry when it becomes one), and accumulate `δ_b=Σ s(x_a/c)(t−1)(B_ab−1)` only from stored B-row cells. Both phases have a common candidate baseline; exact conditional averaging gives `Phi_new=Phi_old+δ_chosen−Σδ/Q`. Every stored delta is positive, so choose the least absent label if any exists; otherwise choose the lexicographic minimum `(delta,label)`. The entire selected trace remains identical.

Potential-state storage becomes **O(K+M)** rational values, excluding graph/trace and the unchanged dense Q×Q load output. Scoring is support-sensitive, bounded by O(MQ+VQ), not a better worst-case Q order than the array-factorized method. Full candidate output, if explicitly requested, is still materialized and charged. The ordinary interface and all three benchmark branches request the same selected trace and final dense loads, not full candidate vectors. This reuses a prior general delta technique, not a claim of new sparse conditional-expectation theory.

The final three-method benchmark includes a filled control (one matching with M=256,Q=8,512 vertices, all64 cells positive) and captures/asserts source and benchmark hashes at both start and end. The frozen final ledger `tree_checks/matching_factorized_benchmarks.json` shows sparse gains over the stronger array-factorized method of1.91–3.87× on random fixtures,4.79× on the parallel-edge fixture,2.04× on the96-edge single matching, and1.58× wall/1.50× CPU on the256-edge fully filled64-cell control. All11 fixtures and old dense/array regressions remain in the ledger. No sparse regression occurred in this bounded set; no universal or SAT speedup is inferred. Source/benchmark start/end hashes agree; details and full ratio table are in `sparse_matching_new.md`. No further algorithmic changes or search are planned.
