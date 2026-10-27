# Review of matrix-partition, adaptive-four, and rectangular packets

> Closing refinement: `four_plan_portfolio_new.md` strengthens the cached headline to **30.491276185937… time /28.853020941407… space**, with safe eventual coefficients **30.492 /28.854**, on the same retuned schedule. The three-plan results below remain valid intermediate comparisons and proof dependencies.

Pinned corpus: supplied by root at ProveIt `73dfb5e5ab6e91bd7375e5b97ef85d7e1cc8e81d`; newest addition `b9941a...`. Incoming programs were **not executed**. Review covered README, TeX proofs and static Python code. New checks in `matrix_checks/` were authored independently for this iteration.

## Important result first

The strongest useful new composition is **not** a retuning of the adaptive-four packet: another new packet, `sat_adaptive_tree_certificate_2026-10-26`, already gives general-degree time **30.891018920366** and space **30.753912832055**. Combining its *unchanged* three-plan menus and `9→13→7` schedule with the genuine rectangular backend of `subsat_rectangular_2026-10-26` proves the strictly smaller pair

- time **30.629497100307…**, eventual coefficient **30.630**;
- space **29.985755335168…**, eventual coefficient **29.986**.

These coefficients multiply `s/sqrt(ceil(log2 s))` in the base-two exponent. Space is subexponential. The reduction in the respective displayed coefficients is about 0.8466% and 2.4978%; these are not measured runtime/speedup percentages. The root agent and tree reviewer were notified immediately.

This is an explicitly credited cross-packet composition, not a claim that rectangular multiplication or adaptive tree selection is new. Its new contribution is the concrete combined local certificate, exact exhaustive verification, and resulting paid global bound. No stronger logarithmic SAT order follows.

## Assigned packets and strongest claims

| Packet | General-degree polynomial-space coefficient | General-degree cached time / space | Main new ingredient |
|---|---:|---:|---|
| `sat_adaptive_matrix_partition_2026-10-26` |50.210434836331|34.325282797285 /34.024178007491| Second-moment bounds for adaptive nine-group triples and sixteen-leaf streamed separators |
| `subexponential_sat_adaptive_four_2026-10-26` |50.393725700505|32.915813864924 /31.661706786194| Sharp adaptive matching inequality on four blocks; full paid multistage schedule |
| same, optional `ω=19/8` |same|32.856345276006 /31.467483188098| Smaller established square exponent in its parametric lemma |
| `subsat_rectangular_2026-10-26` |53.9775311981|33.9938908592 /33.9937208906| Genuine rectangular bridge using dual exponent >.3 and square exponent <19/8; new asymmetric Hermite and representation barriers |

These all improve on some previous iteration headlines, so the former 55.331622 polynomial-space and 35.070614 cached time should not be advertised as current-best. However, *other* newly supplied packets already dominate these assigned packet numerical headlines. The matrix-partition cached point's space is slightly worse than the former 33.999502 point, but the adaptive-four and tree-certificate points dominate both coordinates anyway. Low-degree specializations, including our former `degree≤s^.51` result, must be kept in a separate premise column rather than compared numerically against the generic branch.

All three use the common normalized interface: at most `s` Boolean wires, maximum degree `ceil(s^.9)`, polynomially many vertices and polynomial tensor-description length; root precision/truncation lengths ≤s (fixed multiples also work); admissible original entries cost `poly(s+L) 2^{O(s^.9)}` and polynomial space; immutable creation-precision representatives. Arithmetic is over `(Z/2^p Z)[U,V]/(f(U),V^ell)` with polynomial module rank, `deg f=O(log s)`, and polynomial coordinate bit lengths. They retain the upstream deformation, Cauchy mode factorization, Hermite recovery, packing and SAT-reduction dependencies. They do not provide independent certification of the full ETH claim.

## Matrix-partition proof assessment

The nine-group proof uses exact list-logarithm norm `||h||₂≤(1+o(1))K/9`. Combining two orientations gives undirected squared norm ≤`2K²/81`. For 280 partitions into triples, the final triangle's adaptive exponent is bounded by `sqrt(57/175) K`, using exact covariance values 1/2,1/28,−1/21 for equal/adjacent/disjoint edges. The row-sum and incidence-matrix calculation is correct. Binary construction of the three block tables then dominates at `β=sqrt(916)/45`, not the final triangle. The cache factor `α=4/9`, geometric decay `2sqrt(2)/9`, and condition `α/(1−γ)<β` correctly pay all recursive entries. The root storage uses 36 directed boundary pairs, coefficient 2/3.

The streamed sixteen-leaf proof centers path loads and uses a permutation-invariant edge covariance matrix with eigenvalues `0,33/56,85/2912`. Combined with `max deviation≤sqrt(15V)`, it yields `β_ps²=725/1344`. The 14,827-state, 462,465-split subset DP exactly minimizes balanced-tree maximum path cost using integer ceiling logs; additive rounding loss is at most 170. The unchanged precision/packing schedule leads to50.210434836331. This is a coherent proof relative to the listed inherited gates. The optional uniform norm argument via finite-dimensional compactness is valid.

Static `code/adaptive_groups.py` review: exact arbitrary-ring regrouping with naive scalar multiplication; tracks paid singleton-table accesses and largest table. It does not instantiate the asymptotic fast backend, and no SAT performance claim is justified. The 280-partition selector uses exact rational comparisons. `code/adaptive_tree.py` is a finite selector, not a complete SAT solver.

## Adaptive-four proof assessment

The sharp four-block square-backend inequality is `min_matching max_merge_cost≤sqrt(244/75)||w||₂`, with a star-weight equality witness. The proof averages one maximizing support form per matching and bounds correction-vector inner products. Its generalization to `7/3≤ω≤3` gives `sqrt((ω²+4)/3)` on the six undirected edges, hence equal-four-cluster local coefficient `sqrt((ω²+4)/24)`. The correction norm inequality has the correct sign for `ω−2≥1/3`. Complete table construction for r=4,8,12 fits the local bound. The fixed `8→12→8→4` schedule has a nonroot paid-entry term, not root aggregation, as the maximum; this is why its time and space differ.

Its streamed four-cluster inequality has squared directed constant `26/3`, and recursive profile `g(4b)≤(26/3)b²+g(b)`. Combining disjoint supports is legitimate. The complete `16→16→8→4` schedule gives50.393725700505, slightly worse than the matrix-partition packet's polynomial-space headline and now dominated by another packet's 46.184845586731.

Static `code/adaptive_four.py` review: paid callback per singleton entry, naive matrix multiplication, exact fifth-power matching comparison, finite dual-number ring tests. No implemented fast matrix backend or measured SAT speedup. Its exact finite contraction identity can be used independently of the theoretical backend.

I also derived a valid rectangular-four inequality with local squared coefficient `[4v²+(2+w)²]/24=.385313...`, giving32.6578629620 time/30.8192426651 space on the old four-block schedule. This is dominated by the tree-portfolio combination and should be described only as an ablation, not a headline.

## Rectangular proof assessment and imported backend

For sorted logarithmic dimensions `x≥y≥z≥0`, the packet proves

`F=max{d(x+y), x+v y+w z}`,

where `epsilon=1/100000`, `d=1+epsilon/2`, `v=47/56+epsilon`, `w=15/28`. The external facts are only `alpha>.3` and `omega<19/8`, cited to *New Bounds for Matrix Multiplication: from Alpha to Omega*, arXiv:2307.07970. These inequalities do not require a current-record assertion. The tensor product of a fixed rational `N×N^.3×N` algorithm and a fixed square algorithm supplies the intermediate aspect ratios; rounding each fixed-base recursion depth incurs only constant factors. Blocking the longest axis handles unequal large dimensions. Dimension permutation is implemented by permuting the finite tensor decomposition, not by assuming a transposed cached program has free workspace.

**Do not drop the first branch.** `2+epsilon` arithmetic does not imply exactly quadratic total work. The first branch retains the input/output cost and is crucial in the original rectangular certificate. Input/output and temporary arrays fit within a polynomial factor times the largest pairwise dimension product. The integer coordinate/CRT bridge avoids dividing by nonunits in the actual ring. Fixed exceptional primes can be skipped and enough odd primes reconstruct the positive integer coordinate products; polynomial rank/precision bounds keep all bit overhead polynomial.

The matrix cardinality proof `Phi(q)=max{d²(q1+q2),q1+v²q2+w²q3}` with decreasing `q` is a valid uniform upper bound by the rearrangement inequality. The original packet's 8-group bound is output-bound at the root; treating the second branch alone would underpay tables.

The new arbitrary-asymmetric Hermite theorem appears sound: the inactive-node extension makes the independent-jet precision objective convex; averaging residue-tree automorphisms fixing zero gives a valuation-symmetric optimum; backward rational recurrences give the finite real optimum; componentwise ceilings increase the normalized objective by <2. It establishes that the leading six survives *arbitrary node multiplicities* within the fixed independent-error Hermite model. It does not rule out exploiting algebraic correlations among attainable jets.

Its table/tree barrier is correctly scoped to the relaxed entropy norm ball, not to actual SAT or all summation algorithms. A fixed tree has a balanced node, giving ≥2K/3 certificate width. Adaptive trees still have a uniform-positive vector witness, giving ≥`4K/(9sqrt(1−1/r))`. The precision-peeling note correctly says that discarding only a polylogarithmically thin budget tail retains the same leading entropy and inherited precision exponent; a free cumulative-precision reset is not established.

## New rectangular-tree support certificate

Full derivation is in `rectangular_tree_new.md`; exact standard-library verifier and deterministic normal/optimized outputs are in `matrix_checks/verify_rectangular_tree.py` and `verified_rectangular_tree*.json`. An independent NumPy exploratory implementation reconstructed the same maxima before the standard-library checker was authored. No incoming Python was executed.

Let `L=1,400,000`. An operation tripartition has three edge classes. Its 9 possible integer support forms assign permutations of

- `(1,400,007,1,400,007,0)` (output branch),
- `(1,400,000,1,175,014,750,000)` (rectangular branch),

to the classes; within-part edges get zero. The maximum divided by L equals F, by the rearrangement inequality. For the three inherited plans on r vertices, union and deduplicate supports per plan. Averaging the three plan costs gives

`b_r²=2 Q_r/(9r²L²)`, where `Q_r=max ||v1+v2+v3||²`.

Exact results:

|r|supports/plan|all triples|Q|b²|
|---:|---:|---:|---:|---|
|9|57|185,193|246,255,154,308,036|2280140317667/6615000000000|
|13|89|704,969|519,754,477,218,816|24170130079/69316406250|

No minimum/maximum interchange is needed: `min_j max_v v·g≤(1/3)Σ_j max_v v·g=max_(v1,v2,v3)(v1+v2+v3)·g/3`. Apply the inherited weighted entropy estimate to each of the finite fixed support sums. The same local cost bounds all input/output arrays because the output branch dominates every pairwise dimension product. Exact integer-size products, or ceiling binary logs with additive constant loss, choose the minimum-cost plan deterministically in polynomial work.

Retain the exact old r=7 square backend in the tail; changing only r=9,13 local aggregation does not alter child-entry costs, precision, schedule or leaf premises. With `f0=63/4000,f1=9/800,f2=77/16200`, `K0=κ/sqrt(f0)`, `K1=2κ/(9sqrt(f1))`, `K2=4κ/(117sqrt(f2))`, `κ=πsqrt(2)/ln2`, the complete time maximum is

- `C0=b9 K0∈(29.985755335168,29.985755335169)`,
- `C1=(4/9)K0+b13 K1∈(30.629497100307,30.629497100308)`,
- `Cinf=(4/9)K0+(sqrt24/13)K1+(sqrt3/2)K2∈(30.512927432780,30.512927432781)`.

Thus C1 dominates time and C0 dominates space. This improves both coordinates of the strongest comparable incoming generic cached certificate. All-size validity depends on the stated proof and inherited interfaces; finite checks are not a proof of the upstream manuscript.
