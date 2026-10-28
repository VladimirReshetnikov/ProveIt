# Independent frontier audit

**Closing update:** the review was extended to `dde01c4a63b822c25b8eb345299346c36f837b49`. The newly placed `sat_adaptive_contraction` packet is the twentieth refinement packet. It improves the standalone generic polynomial-space coefficient to 55.70947831891 and the cached low-degree branch to 15.3919331988 / 14.2501611298. The detailed closing audit at the end of this note supersedes the initial-snapshot frontier where applicable. The original nineteen-packet assessment is retained below for provenance.

Review snapshot: `VladimirReshetnikov/ProveIt@f898a9fde4c3ed3bbcd53ed45cc79970b7b41d66`.
Read-only source checkout: `ProveIt/`. Four currently incoming archives were extracted into `incoming_review/` after the parent checked member paths. This note reviews actual LaTeX proofs; it does not certify the imported OpenAI manuscript end to end or claim formal verification.

## Comparison target

There are fifteen placed refinement packets plus four currently incoming refinement packets, as well as the two primary manuscripts. The README coefficient 76.909 is stale as a description of the combined frontier. The best **explicit generic polynomial-space** wire coefficient stated in the current corpus is 63.8522033905488...; the best **explicit generic cached** time coefficient is 35.354588058401... at space coefficient 34.274803005023.... These multiply `s/sqrt(log2 s)` where s is a normalized Boolean wire count, not SAT variable count.

All four incoming reports explicitly retain the general-density SAT exponent order `n log log n / sqrt(log n)` and the fixed-density order `n / sqrt(log n)`. The common density envelope is `poly_k(n,m) 2^{O_k(n min(log(2+m/n),log log n)/sqrt(log n))}`. The older `n/log n` denominator claims remain conditional on missing recursive or summation interfaces. Numerical constants in the separate Claude manuscript remain unspecified and cannot be ranked against these wire coefficients.

## Four current incoming packets

| Packet | Generic polynomial-space coefficient | Cached time / space coefficient | Components relevant to asymptotic research |
|---|---:|---:|---|
| `sat_frontier_improvements_2026-10-26` | 63.8574094711 | 38.4844959057 / 34.2748030050 | Multistage arities, cache composition, lower-degree specializations (31.9287 at root degree s^(3/5), 26.9023 at degree s^(1/12)); practical Cauchy-prefix kernel |
| `subexponential_sat_frontier_2026-10-26` | **63.85220339055** | 37.93010908288 / 33.62304092166 | Strict rational multistage polynomial-space schedule; root-7/tail-9 Strassen schedule; exact row-sum caching; precision peeling |
| `subexponential_sat_kernel_improvements_2026-10-26` | 66.6051434076 (explicit composition) | 44.5375718550 / 39.4959495337 | Gray and antipodal coefficient extraction, projective roots-of-unity filter, adaptive Smith separation on actual ports |
| `subsat_contraction_tree_2026-10-26` | Retains earlier polynomial-space methods | **35.354588058401 / 34.274803005023** | Binary construction of cached block tables; exact coordinate/CRT transfer of fixed field matrix algorithm with exponent <12/5; completely charged child-oracle recurrence |

The 35.3546 cached theorem does not dominate the 33.6231 space guarantee: this is a time-space tradeoff. Retaining all methods gives a portfolio rather than one scalar best method under every space allowance.

## Proof audit: cached contraction tree

Primary proof: `incoming_review/subsat_contraction_tree_2026-10-26/subsat_contraction_tree_2026-10-26/report/cached_tree.tex`.

The main points checked are sound under the imported contraction interface:

1. With fixed grouping arity r, arrays of exact directed-pair weights are polynomially numerous. This property would need reanalysis if r grew with s.
2. Group functions are tabulated on their incident pair indices, and every entry is charged to a recursive child contraction. There is no free group-function oracle.
3. The common-tilt estimate `sum z_e h_e <= (sqrt(sum z_e^2)/r+o(1)) K`, `K=pi sqrt(2) M/(ln(2) sqrt(u))`, applies even to small and zero individual pair budgets. This avoids a common invalid per-pair asymptotic substitution.
4. Tables for disjoint group subsets A and B share precisely the directed indices between A and B. Their other indices are disjoint. Their contraction is therefore a rectangular matrix product after reshaping, with index-class cardinalities `2|A|(r-|A|-|B|)`, `2|A||B|`, and `2|B|(r-|A|-|B|)`.
5. A fixed rational bilinear algorithm of exponent strictly below 12/5 can be reduced modulo all but finitely many odd primes. Coordinate products of lifted ring entries have polynomial bit length because log(matrix dimension) and working precision are polynomial. Polynomially many CRT primes recover their nonnegative integer values. Ring multiplication is reconstructed through the known polynomial-rank module multiplication table. No illegal nonunit inversion in the 2-adic quotient ring is hidden.
6. For root arity 8 and balanced final blocks (3,3,2), the largest merge squared cost is 766/25; triangle squared cost is 798/25; boundary cardinality is 30. For tail arity 12 and blocks (4,4,4), these are 1632/25, 1728/25, and 64. The triangle dominates binary table construction.
7. The recurrence `T_d <= 2^{a_r K_d} T_{d+1} + 2^{b_r K_d}` includes both recursively evaluated group tables and local contraction. Its unrolling and the maximum of the root and tail costs are correct. Memory is a sum of stored tables along a path, so its leading exponent is a maximum, not a sum.
8. The explicit threshold `H=s/lambda^(3/4)` matters for the tail taper: it ensures the minimum active u_d diverges. Simply changing H to s/lambda with the same factor-six taper would not preserve that argument.
9. Every root/tail packing gate has strict positive slack. The inherited degree bound, immutable creation-time descriptions, logarithmic precision buffer, lower-order entry oracles, and polynomial arithmetic lengths are explicitly included.

No fatal gap was found in these new steps. This is an audit of these steps relative to the imported identities, not a proof of the entire underlying SAT algorithm.

## Proof audit: exact local kernels

Primary proof: `incoming_review/subexponential_sat_kernel_improvements_2026-10-26/subexponential_sat_kernel_improvements/report.tex`.

The adaptive separator is minimum-valuation Gaussian elimination over an unramified chain ring. Taking a minimal-valuation pivot makes the normalized pivot a unit; division by its power of two is exact at the reduced precision. Canonical-lift ambiguity is killed by the pivot-column valuation. The resulting weights are the Smith invariants. The profile domination argument uses minimal generator count of finite chain-ring modules, equivalently their socle dimension; containment indeed bounds this count. Thus the claimed dominance of weighted mode inventories over every other integral separated representation of the same actual block is justified.

For real slots in an arithmetic progression of step valuation i+h, the exact weights are `delta+(2h+2)j-2 popcount(j)`. This gives an instance-specific slope gain when h>1. It does not provide a uniform gain for arbitrary SAT encodings or arbitrary allowed packets. The prior actual-domain rank-gate report exhibits filled permissible packets with exact slope-four Smith profile, blocking a universally superlinear integral separated basis on that family.

The projective coefficient filter correctly fixes a coordinate of minimum target exponent: the retained congruence class cannot alias another monomial of the same homogeneous degree. A nonminimal fixed coordinate could alias, as the report explicitly warns. The requisite roots-of-unity orthogonality is stronger than multiplicative order over rings and is explicitly imposed. Its one/two-exponent implementation verifies the cubic relation at augmented precision.

The antipodal coefficient-extraction identity is correctly integral even in the all-even case: its formal factor 2^(-1) is canceled by a factorial. The zero center vanishes for positive homogeneous degree. Its precision loss, grid count, and canonical representative convention are consistent.

These are exact subroutine improvements. They do not by themselves alter the logarithmic SAT exponent.

## What remains open

The relative model still has linear Cauchy/Smith weights, partition entropy of order M/sqrt(u), and packing restrictions u=O(log s). A change in a constant matrix exponent, a fixed grouping arity, a fixed mode slope, or strict scheduling slack only changes leading constants. Missing-degree and structured summation interfaces in the older reports must actually be constructed to justify a smaller order.

The strongest older conditional target is the structured-mode-summation implication in `3sat_precision_refinement`: `n log log n/log n` generally and `n/log n` at fixed density. Another conditional interface yields `sqrt(sK/log s)` and hence `n sqrt(log log n/log n)` when s=Theta(n log log n), K=Theta(n). These are implications from explicit unproved algorithmic interfaces, not existing algorithms against which an unconditional speedup can be claimed.

A modest explicit further coefficient improvement is available by reducing conservative slack in the contraction-tree schedule; for root arity 8 and field exponent allowance 12/5, its root-capacity boundary is approximately 35.063598846 on the same scale. This is weaker evidence than an order-level result and should not be described as resolving the missing interfaces. Further multi-stage cached schedule exploration is recorded separately as numerical research, not a certificate.

## Complete proposal classification and source locations

All entries called proved below mean ordinary mathematical derivations **relative to the unchanged source contraction/reduction framework**, not a new independent verification of the source ETH claim.

| Packet | Proved component / best stated bound relevant here | Unproved route or scope limit | Precise proof location |
|---|---|---|---|
| cauchy_mode_improvement | Factorial Cauchy weights of slope 3; 1/sqrt(3) enumeration-coefficient ratio | Same SAT order | `report.tex`, `thm:weights`, `prop:recursion`, `thm:global` |
| eth_contraction_improvements | Exact Hermite taper and precision, streamed packet extraction, C=648.4410666 | Same SAT order | `report.tex`, `thm:main`, `thm:packet`; enumeration obstruction proposition |
| 3sat_precision_refinement | Exact precision and optimal full-loss taper | Structured acceleration hypothesis yields s/log s contraction, n log log n/log n SAT | `report.tex`, `thm:precision`, `thm:optimal`, `hyp:acceleration`, `thm:conditional-contraction`, `cor:conditional-general` |
| sat_density_improvement | Uniform density envelope with min(log(2+m/n),log log n) | Same worst-case and fixed-density order | `density_aware_sat_improvement.tex`, `thm:main`, `cor:intermediate` |
| eth_density_refinement | Same density dependence (polylog-density premise before hybridization), precision savings | Same unrestricted order; actual Cauchy linear Smith obstruction | `report.tex`, `thm:density`, `cor:hybrid`, `subsec:smith`, `eq:smith` |
| 3sat_refinement | Scalar parity lift, incidence degree k(p+a−1), scalar ring replacement | Missing compact factorization yields n(log log n)^(3/2)/log n | `3sat_refinement_report.tex`, `thm:cap`, `cor:replacement`, `thm:conditional`, `cor:conditional-sat` |
| 3sat_asymptotic_analysis | Scoped barriers and exact missing interfaces | Degree-preserving interface yields sqrt(sK/log s); linear-wire interface also unconstructed | `research_runtime/CONDITIONAL_DEGREE_KERNEL.tex`, section `sec:conditional-degree-kernel`; `report/research_routes.tex` |
| eth_asymmetric_packet_balancing | C=76.9089949, polynomial space; asymmetric degree invariant | Low-degree C=31.0641321 has Δ≤s^(1/12) | `report.tex`, `thm:main`, `thm:pair-balance`, `cor:padding`; low-degree section |
| 3sat_round2_refinement | C=84.06627, polynomial space | Actual-domain rank gate rules out uniform superlinear local integral mode weights | `report/combined.tex`, `thm:85`; `report/actual_domain.tex` |
| eth_balanced_packing | C=94.7482023, polynomial space | Same SAT order | `report.tex`, `thm:labeling`, `cor:packets`, `thm:main` |
| eth_high_moment | C=94.7482023, polynomial space | Degree-sensitive values 42.3727 and 31.2365 require stronger inputs | `report.tex`, `thm:main`, `cor:padding`, degree-sensitive sections |
| eth_matching_refinement | C=94.7482023, polynomial space | Same SAT order | `report.tex`, `thm:main` |
| eth_packet_refinement | C=95.66394, polynomial space | Same SAT order | `report.tex`, `thm:balance`, `cor:unitpadding`, `thm:main` |
| eth_recursive_refinement | C=133.20737, polynomial space; slope64/21 annular modes | Sparse-query specialization60.70696 has stronger input bounds | `report.tex`, `thm:main`; `kernel.tex` |
| eth_joint_cauchy | C=319.685757 polynomial space; cached225.597057 /196.199446 | Full-block exact Smith slope4 with multiplicity, supports later compositions | `report.tex`, `thm:main`, `thm:fast`, `thm:modes`, `cor:smith` |
| sat_frontier_improvements | C=63.85740947 polynomial; cached38.48449591 /34.27480301 | Low-degree polynomial31.9287,26.9023; cached19.08387 /16.99635; still same order | `sections/variable_arity.tex`; `sections/cache_composition.tex`, `thm:cached-eight`, `cor:cached-lowdegree`; `sections/degree_corollaries.tex` |
| subexponential_sat_frontier | C=63.85220339 polynomial; cached37.93010908 /33.62304092 | Same SAT order; exact arithmetic kernel improvements | `report.tex`, `thm:ps`, `thm:cached`; `theory.tex`, `sec:theory`, `sec:cache-theory` |
| subexponential_sat_kernel_improvements | C=66.60514341 composition; adaptive Smith profile optimal among integral separated representations | Adaptive improvement is support-specific, not uniform across full actual packets | `report.tex`, `thm:smith`, `thm:domination`, `cor:stride`, `thm:antipodal`, `thm:projective` |
| subsat_contraction_tree | C_time=35.35458806, C_space=34.27480301 | Subexponential memory; complete source interface retained | `report/cached_tree.tex`, `thm:cached-tree`, `lem:coordinate-bridge`, `eq:tree-recurrence`, `eq:tree-total-time` |

### Exact root classes

The generic normalized input class is a bipartite Boolean tensor network with ≤s wires, polynomially many vertices, maximum degree ≤ceil(s^(9/10)), and initial precision and nilpotent truncation length O(s). Original entry routines run in `(s+description_length)^b 2^{A s^(9/10)}` time and polynomial space, for fixed A,b. Coefficients are in `(Z/2^P)[V]/(V^ell)` initially, with polynomial-degree unramified extensions used in recursion. Creation-time representatives must remain frozen.

The normalized coefficient comparison changes if one rescales s or allows a different hidden initial edge-count constant. New results must either use exactly this class, state a stronger degree premise, or track the normalization explicitly. No reviewed wire coefficient can be substituted directly for a coefficient multiplying n in a SAT bound.

In the low-degree cached corollary of sat_frontier_improvements the exact constants are

- time `pi sqrt(30)/(8 ln2) sqrt(30+12(log2(7)−2)^2) = 19.083872848507685`;
- space `30 pi/(8 ln2) = 16.996350531851974`.

These are valid under root degree ≤s^(1/12), maintained internal degree≤s^(1/7), and the otherwise same oracle allowance. A new generic theorem at C≈35 does not dominate that stronger-premise guarantee; retain it in a portfolio.

## Adaptive Smith dominance: correctness and exact scope

The pointwise comparison has no identified gap. Over the finite unramified chain ring R_p, a nonzero cyclic summand `R_p/(2^a)` has a one-dimensional socle over the residue field. Every finite module is a direct sum of such cyclic modules. Consequently its minimum generator count equals its socle dimension. If image(K) is contained in the submodule spanned by N surviving rank-one target columns, socle inclusion gives generator count≤N. Reducing modulo2^q proves `#{e_h<q}≤#{w_j<q}` and thus coordinatewise `w_h≤e_h` after sorting. Zero modes may be removed; zero target weights simply make the inventory lower bound easier under a finite ordinary-degree cap.

The theorem assumes **integral separated** factors over the chain ring. It does not constrain fractional/nonintegral factors with global cancellation, arbitrary nonseparated algorithms, or a support-specific representation of the whole tensor network. Allowing nilpotent V in the factor vectors does not evade the constant-kernel comparison: specializing V=0 recovers a representation over the chain ring with the same guaranteed powers of2. Ramified extensions or a different uniformizer/precision model would require separate analysis.

The exact full-block profile at arbitrary i is already present in `eth_joint_cauchy/report.tex`, `cor:smith`: each `delta+4q−2popcount(q)` occurs `R=2^i` times, q=0,…,D/2−1, delta=a+1−i, D=2^(a−i). Its triangular factors have unit diagonal after the stated valuation normalization. The i=0 minor argument in the density report and actual-domain rank gate agrees with it.

## A strengthened explicit inventory and dense-table barrier

A formal statement and proof are in `research_notes/adaptive_inventory_barrier.tex`. This combines the existing exact profile with the adaptive optimality theorem and an exact-weight pigeonhole argument. It covers all integral basis substitutions on the full real-port family, and also explicit exact-weight table construction, whereas older abstract counting barriers did not directly include the newer adaptive separator and cached tables.

Take A copies of each mode weight `delta+4j−2popcount(j)`, j=0,…,J−1, and let M=AD. Suppose u≥1, D≥16sqrt(u), delta≤D/sqrt(u), J≥floor(D/(8sqrt(u))), and integer P≥AD²/(4u). Then every integral separation of the corresponding direct-sum kernel has at least `2^{M/(16sqrt(u))}` binary feasible tuples of weight<P and ordinary degree≤M. This is proved by selecting the first q=floor(D/(8sqrt(u))) Smith weights in each copy. Their total is at most `A(q delta+2q(q−1))≤5AD²/(32u)<P`.

These tuples occupy at most P exact total weights, so some exact-weight list has at least `2^{M/(16sqrt(u))}/P` members. For a fixed grouping alphabet, a directed pair containing a fixed positive fraction of full crossing blocks still gives the same Omega(M/sqrt(u)) scale. Any prescribed method that explicitly materializes each entry of the resulting group table has at least that many cells to write. Since P is polynomial in root size and u=O(log s), this is an exponential-order obstruction within the explicit-inventory/dense-table model.

The conclusion does not say that all resulting tensor coefficients or table entries are nonzero, distinct, or hard to evaluate. An algorithm that detects algebraic zeros, combines correlated terms, or represents the group function compactly without materializing every formal index can evade the bound. It is not a complexity lower bound for SAT or general tensor contraction. Per-packet row-degree caps are also respected when separation is done per original full orientation: at most Rq≤L/2 selected modes per packet. Arbitrary cross-packet basis mixing has only the asserted global degree cap unless additional support information is tracked.

## Closing update: twentieth packet and new prior envelope

Closing snapshot: `dde01c4a63b822c25b8eb345299346c36f837b49`. Placement commit `450252e9d86c155f188b485629b9755c5c665371` added `sat_adaptive_contraction`, from arrival `fa6e904d10`. Its primary source is `ProveIt/Computability/SubexponentialSAT/Research/sat_adaptive_contraction/adaptive_sat_review.tex`.

### Exact new scope

| Branch | Time coefficient | Space coefficient | Proof labels |
|---|---:|---:|---|
| Generic polynomial space, recursive conditioning | 55.70947831890997 | polynomial | `lem:stream-exact`, `lem:stream-profile`, `thm:ps` |
| Generic cached, adaptive partition into triples | 36.75031252383623 | 34.024… | `lem:partition`, `thm:local`, `thm:main` |
| Cached at root degree ≤s^(1/12) | 15.3919331988 | 14.2501611298 | `cor:low` |

The generic cached branch is slower than the earlier contraction-tree certificate35.354588 but uses less memory; the low-degree branch supersedes the earlier19.08387/16.99635 branch under the same root-degree premise. Every coefficient remains on s/sqrt(log2 s), and all inherited root/oracle/precision conventions remain in force.

### Recursive-conditioning proof audit

For one exact weight array, every group-pair domain is independent because the global budget has already been fixed by the array. Splitting a group set A∪B and conditioning on pair indices crossing A/B separates its internal variables. Finite distributivity gives a product of two conditional sums, then a sum over the cut indices. This is valid in the original commutative coefficient ring, including its nilpotents and zero divisors.

A singleton group factor is reached once per assignment to the disjoint cuts on its root-to-leaf path. Thus its true child-oracle call count is the product of the corresponding domain sizes. Counts **sum** over leaves; sibling internal index domains are not multiplied together. Re-evaluations under irrelevant ancestor assignments are already included in the path product. Every internal visit count is bounded by a descendant leaf count. Polynomial-space depth-first evaluation is therefore valid, and the stated child-oracle cost has not been hidden.

Balanced splitting gives `v(1)=0` and `v(r)=2 floor(r/2) ceil(r/2)+max(v(floor(r/2)),v(ceil(r/2)))`. For r16 this is170 versus240 directed pairs in the full Cartesian sum. The exact pair-subset entropy bound consequently gives local coefficient `kappa sqrt(v(r))/r`, where `kappa=pi sqrt2/ln2`. The factor `sqrt(17/24)` is the ratio of these two **summation organizations** at r16. It is not a new universal per-pair entropy constant and cannot simply multiply a cached coefficient such as34.

The boundary schedule with sublinear `ceil(sqrt(lambda))` reserve has sufficient slack: its negative root and old-side exponent term is −Theta(sqrt(lambda)), larger than all O((log lambda)^2) buffer losses. The tail range ratio1/4 versus eventual child shrink≤1/6 gives a positive-power minimum taper at all active levels. No fatal issue was found in this proof.

### Adaptive cached proof audit

A uniformly random partition of nine groups into triples separates each directed pair with probability3/4. Choosing the exact-weight-array partition that minimizes crossing weight therefore gives crossing exponent at most3/4 of the total, and hence ≤K/sqrt2. Caches of the nine true child functions cost coefficient4/9, block-table construction costs sqrt42/9, and boundary storage costs2/3. Since1/sqrt2<sqrt42/9, direct crossing enumeration is below block construction. The recurrence includes both child-cache evaluation and block construction; its claimed36.7503 coefficient is compatible with this proof.

Combining adaptive partition selection with a different rectangular/tree backend would require a new joint worst-case bound. Neither the3/4 crossing average nor the17/24 path count is a license to scale the new rectangular certificate uniformly. The source has no such assertion.

### Stronger composed prior polynomial-space comparator

Applying the new recursive-conditioning local cost to the already-existing `subexponential_sat_frontier` schedule gives a stronger prior-compatible upper bound than55.709:

- arities13,14,8,6,4 thereafter;
- retained fractions27/2000,51/4000,141/20000,107/20000, then(27/6400)(5/8)^j;
- path cardinalities118,132,42,24,10;
- size factors1,2/13,2/91,1/182,1/546;
- resulting coefficient approximately **55.40466590661055**.

This is a direct composition, not a global optimum. It should be included when comparing any proposed new polynomial-space schedule to the closing corpus. The new r16,16,8,6,5,4 schedule under review targets coefficient53.9775311981 and is audited separately in `independent_new_results_audit.md`.

### Closing provenance and validation record

The nineteen-packet count above is the **initial cutoff**, not the final reviewed corpus. The final reviewed corpus contains twenty refinement packets at closing pin `dde01c4a63b822c25b8eb345299346c36f837b49`, including placement `450252e9d86c155f188b485629b9755c5c665371`. The parent verified byte identity for180 files from the four initially incoming packets after their placement; the closing adaptive packet was then read and audited from its placed source. This note relies on the parent's180-file comparison rather than presenting it as an independently repeated byte audit.

The new streamed schedule's independent exact-checker output is:

- proposed polynomial-space coefficient: `[53.97753119806754, 53.977531198072846]`;
- stronger composed prior coefficient: `[55.404665906606695, 55.404665906612024]`;
- latest packet's standalone coefficient: `[55.709478318909945, 55.70947831891013]`.

The exact rational gates are all strictly below1. The generic cached adaptive packet's exact memory coefficient is34.02417800749051; its stronger-premise low-degree branch remains15.3919331988 time and14.2501611298 space. The original coefficient-frontier rows should be read together with these closing updates.
