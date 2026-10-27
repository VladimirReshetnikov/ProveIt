# Audit of the SubexponentialSAT comparison baseline

Final reviewed snapshot: `VladimirReshetnikov/ProveIt@6d3adc45061535ebe6fa7cd3d9b37dff7dcfc22a`.
The final research subtree is `369f8df31ef68b6b230e95dc2caed42ccd9bd9be`. Initial review used `ab2fbc9e03d5c3d0ad6dec8686960bfe498b0b06` and incoming addition `3e57705cf14ee9ac99c0ac35cfff751dcf70b396`. A closing update placed eight additional packets, including the newly inspected matching refinement, under canonical research paths.

This audit covers fifteen packets: the seven initially indexed packets and eight later packets now under `Computability/SubexponentialSAT/Research`, the project index, and the relevant upstream quantitative-contraction source. It is an analytic and interface review, not a proof-assistant build or an end-to-end execution. Statements described below as established are ordinary mathematical claims relative to the unchanged imported preprint machinery; the repository explicitly does not certify the entire development.

## 1. The strongest justified SAT order in this corpus

For fixed clause width `k`, let `n` denote declared variables and `m` clauses. The strongest density-dependent bound already present is

`poly_k(n,m) * 2^{O_k((n/sqrt(log n))*min{log(2+m/n),log log n})}`,

with polynomial space and constants uniform in the density. For unrestricted density its exponent is still `O_k(n log log n/sqrt(log n))`; fixed density gives `O_k(n/sqrt(log n))`.

Sources:

- `ProveIt/Computability/SubexponentialSAT/Research/sat_density_improvement/density_aware_sat_improvement.tex`, Theorem `thm:main` and Lemma `lem:sparse`.
- `.../eth_density_refinement/report.tex`, Theorem `thm:density`, Lemma `lem:query`.
- `ProveIt/Computability/SubexponentialSAT/README.md`, trust status and strongest-improvements sections.

The strongest conditional target is `poly(n,m) 2^{O(n log log n/log n)}`, and `2^{O(n/log n)}` at fixed density, in `3sat_precision_refinement`. It depends on a uniform structured-mode summation procedure with `exp(O(M/u))` recursive cost, polynomial descriptions, admissible children, preserved precision and polynomial space. That procedure is not supplied. The report explicitly warns against presenting the conditional consequence as an implemented or established SAT algorithm. See `notes/conditional_theorem_review.md`, Sections 1–3. Neither the later eight packets nor their table methods closes that hypothesis.

The separate Claude manuscript has the same relevant unrestricted `n`-order, and gives no directly comparable explicit normalized leading coefficient. It cannot be claimed numerically dominated by a new normalized contraction coefficient without deriving its hidden constants on the same interface. The upstream Lean endpoint reviewed in the archived material uses a weaker `n(log log n)^2/sqrt(log n)` scale; beating that endpoint alone would not beat the manuscript's Appendix D.

## 2. Packet inventory and present strongest explicit constants

All coefficients below multiply `s/sqrt(log_2 s)` in the base-two exponent, where `s` bounds root edges, precision and truncation and root maximum degree is at most `ceil(s^0.9)`. They are not SAT-variable coefficients.

| Packet | Established change or individual certificate | Limitation |
| --- | --- | --- |
| Indexed `eth_contraction_improvements` | Exact taper, leading precision 6 rather than 24, coefficient 648.441066649; streamed finite differences | Same logarithmic order; prototype kernel only |
| Indexed `cauchy_mode_improvement` | Factorial Cauchy weights of slope 3 | Factor `1/sqrt(3)` in leading mode entropy only |
| Indexed `3sat_precision_refinement` | Exact recovery loss and optimal real full-loss taper | Faster summation remains hypothetical |
| Indexed `sat_density_improvement` | Density-aware envelope above | Worst-case and fixed-density orders unchanged |
| Indexed `eth_density_refinement` | Same density envelope; local odd-unit Smith profile | Does not itself realize all-level full-block modes |
| Indexed `3sat_refinement` | Scalar parity lift; degree cap `k(n+a)` | Smaller-order second contraction lacks factorization |
| Indexed `3sat_asymptotic_analysis` | Restricted barriers and precise missing interfaces | No stronger general bound |
| Later `eth_recursive_refinement` | 133.207372492; residue-aware slope `64/21` | Finite sampled inventories can favor the older basis |
| Later `eth_packet_refinement` | 95.663940473 | Symmetric balancing, fixed rational schedule |
| Later `eth_high_moment` | 94.748202260 | High-moment labeling is polynomial only with fixed moment order |
| Later `eth_balanced_packing` | 94.748202260 | Essentially the same leading balanced schedule bound |
| Later `eth_matching_refinement` | 94.748202260 | Matching conditional potential and adaptive integral schedule; no new extraction kernel |
| Later `3sat_round2_refinement` | 84.066271494 | Matching potential; root/tail alphabet schedule, symmetric degree bound |
| Later `eth_asymmetric_packet_balancing` | 76.908994952 | Exploits fresh-side degree; still slope-3 modes |
| Later `eth_joint_cauchy` | Slope-4 full-block modes; individual coefficient 319.685757078 | Its explicit schedule is older and much weaker than the newest schedule |
| Same joint packet, more memory | Time 225.597057284, space 196.199445518 | Fully costed caches and Strassen; sacrifices polynomial space |

The asymmetry packet also has a boundary infimum 76.432773686 for its fixed `r=16` schedule family, and a separate stronger-input low-degree specialization. Neither is a coefficient for arbitrary SAT input size. The boundary number is not a global optimum over all combinations of schedules.

## 3. Required composition before advertising improvement

The strongest individual number is not the strongest compatible baseline. The full-block slope-four basis composes with the asymmetric schedule without changing any graph, group or precision invariant. A defensible comparison must include this composition.

### 3.1 Why the interfaces match

`ProveIt/Computability/SubexponentialSAT/Research/eth_joint_cauchy/report.tex`, Theorem `thm:modes`, constructs

`W_xy(T) = sum_b A_b(x) G_b(y)`

over each whole crossing orientation. For `R=2^i`, `b=qR+r`, the guaranteed weight is

`a+1-i+4q-2 popcount(q)`.

There are exactly `R` modes for each `q` in each of the two orientations of an unequal-symbol packet. The original tile inventory has the same multiplicity. Each source feature reads only columns in one source group, and its target coefficient is used only in the other group. Auxiliary padded pivots need not be real ports. Thus graph wires, child grouping and new packet vertex degrees remain unchanged.

The factors are integral over the actual unramified coefficient ring, including non-prime interpolation elements. The proof uses only ordinary integer factorial valuations and factorwise division with known total nonnegative valuation. No invalid assertion that an arbitrary extension element has integral binomial values is needed. Scalar source/target factors extend coordinatewise to the truncated coefficient ring with nilpotents. This is stronger and simpler uniformly than the local annulus/residue bases.

`ProveIt/Computability/SubexponentialSAT/Research/eth_asymmetric_packet_balancing/report.tex`, equations `eq:family-count`, `eq:sharp-precision`, and `eq:main-schedule`, gives

- near-unit padded mass `P=(1+o(1))M`;
- at most `(2(1-1/r)+o(1))M/D` mode families;
- child size `(2/r+o(1))M`;
- leading precision `(6+o(1))MD/u`;
- root `u_0=floor(lambda/81)`, tail `u_d=floor(lambda/(108*4^(d-1)))`, `r=16`;
- additive precision gap `ceil(6 log_2 lambda)`;
- unchanged immutable creation-precision tensor descriptions.

Replacing only the basis leaves all of those facts valid. The local natural-log entropy coefficient becomes `pi*sqrt(2(1-1/r))`, instead of `pi*sqrt((8/3)(1-1/r))`. Consequently the polynomial-space combined certificate is

`C_PS = (sqrt(3)/2)*76.90899495160009 = 66.60514340761482`.

The fixed-`r=16` boundary version is approximately `66.19272369360957`. These are explicit comparison examples, not the best of all possible schedule combinations. The parent analysis found a still smaller two-stage boundary value `66.12047546` with root alphabet 17 and tail alphabet 13. A new schedule can improve these numbers, but straightforward basis/schedule composition itself is not a new structural theorem.

### 3.2 A stronger resource-matched comparator when exponential space is allowed

The joint packet's exact-weight indexing, cached child functions, three block tables and division-free rectangular Strassen construction also composes with the asymmetric schedule. Its derivation must be redone at `r=16`; copying the packet's `r=256` numerical coefficients would be incorrect.

At each directed group pair, uniform padding gives at most `(2+o(1))M/(r^2 D)` colors of each full-block index. The weighted entropy lemma therefore has scale

`K(M,u) = (pi*sqrt(2)/ln 2) M/sqrt(u)`.

Split the 16 groups into blocks of sizes 5, 5, and 6. For the root scale `K_0 = 9 pi sqrt(2)/ln 2 = 57.687526639181364`, the relevant factors are

- individual cache: `a_0=sqrt(30/256)=0.3423265984407288`;
- block construction: `a_B=sqrt(150/256)=0.7654655446197431`;
- boundary-table storage: `j_B=sqrt(120/256)=0.6846531968814576`;
- rectangular Strassen, with `omega=log_2 7`:
  `b_S=sqrt((170-[1-(omega-2)^2]*50)/256)=0.7720485597091372`.

The three inter-block directed-pair counts are 50, 60, and 60. The coefficient discounts the smallest class because rectangular multiplication is bounded by the maximum of the three weighted sums.

The first child scale obeys `K_1/K_0=sqrt(3)/12`, and each later scale decreases by 1/4. The full time recurrence is

`T_d <= poly(s) [2^{(a_0+o(1))K_d} r T_{d+1} + 2^{(max(a_B,b_S)+o(1))K_d}]`.

Root matrix work dominates: at depth one its normalized coefficient is `a_0+b_S sqrt(3)/12 < b_S`, and later cache prefixes remain below `a_0(1+sqrt(3)/9) < b_S`. Thus the compatible more-memory certificate is

`C_time = K_0 b_S = 44.53757185496246`,

`C_space = K_0 j_B = 39.49594953369977`.

The exact-weight allocation arrays and mode indexing are polynomial-size because the group count is fixed. The source packet supplies sequential-table access and reordering arguments to avoid assuming free random access. Its group values are paid recursive contractions, not unproved cheap oracles. This comparison is therefore justified in the same model, with the stated space cost. It does not improve the logarithmic order.

## 4. Audit of key new packing claims

The asymmetric two-stage lemma is sound at the inspected algebraic level. Greedy whole-row labeling gives `W_a <= M/Q + R`. With `q=1+1/(h C)`, the exact conditional potential is `sum_(a,b) q^{X_ab}`. Convexity gives the expected potential bound and then

`max X_ab <= (1+2/(h-1)) (M/Q^2+R/Q) + 2(hC+1) ln Q`.

Its denominators and exponents have polynomial bit length; exact conditional expectations are constructive. The near-unit padding conditions are `QR/M=o(1)`, `Q^2 C (log s)^2/M=o(1)`, and `LQ^2/M=o(1)`. The crucial fresh-side bound `C_d<=2L_(d-1)` follows from the actual child bipartition: all retained old tensors go to one side; only newly created packet tensors occupy the other. This is stated explicitly in upstream `quantitative-contraction.tex`, subsection `subsec:tensor-children`.

The inspected schedule avoids circular depth arguments by verifying all hypothetical depths in a coarse range first and then proving shrinkage excludes deeper active calls. Its exact root slack is small (`1/810` in an exponent), which underscores that no realistic runtime benefit follows from the eventual theorem alone.

The round-two matching-potential proof similarly avoids assuming independence across matchings: it only uses independence within a matching and linearity of expectation. Its explicit `K<=2 Delta-1` greedy multigraph edge coloring and rational conditional expectations make the asserted polynomial construction plausible and inspectably valid. These observations are scoped analytic checks, not a complete line-by-line verification of all fifteen papers.

## 5. Practical extraction kernel: novelty boundary and implementation cautions

The eight later packets reuse the older streamed coefficient extraction. The final matching packet was separately inspected in full: its report and `code/refinement.py` introduce matching-based packing, exact parameter schedules, precision calculations and abstract weighted counts, but no Gray, antipodal or projective coefficient extractor. Search across the authored TeX, Markdown, text and Python corpus found no Glynn/Ryser formula, Gray-code traversal, centered coefficient grid, or paired half-grid extraction. The only centered powers are unrelated moments used in packing. Thus a Gray/symmetry extraction kernel is a new implementation direction relative to this corpus, while the underlying identities may be classical and should be attributed accordingly.

The existing implementation is `ProveIt/Computability/SubexponentialSAT/Research/eth_contraction_improvements/code/packet_extraction.py`, function `coefficient_finite_difference`. It recomputes all row values from all grid coordinates at each point of the Cartesian grid, then multiplies all row values. It already preserves polynomial space, supports general monic coefficient extensions and truncated nilpotents, canonically fixes input coefficients at creation precision, and uses sufficient precision for factorial division. A replacement must preserve all of those correctness properties.

For a homogenized degree-`R` product and exponent vector `b` summing to `R`, let `G=product_j(b_j+1)` and `v=sum_j v_2(b_j!)`. The old finite-difference routine works modulo `2^(p+v)`. A centered grid `x_j=b_j-2 gamma_j` has antipodal pairs. The two paired contributions agree because both the sign weight and the homogeneous polynomial change by `(-1)^R`. For `R>0`, any unpaired all-zero center contributes zero. Thus only `floor(G/2)` evaluations are required. Taking the pair factor two out symbolically leaves denominator `2^(R-1) product_j b_j!`, so this uniform-step version needs working precision `p+R+v-1`. The final implementation improves this further: use unit-step centered grids for even exponents and step-two grids for odd exponents. If `O` is the sum of odd exponents, sufficient precision becomes `p+v+O-1`; when all exponents are even, this is one bit less than the baseline. The independent review in `code/INDEPENDENT_REVIEW.md` verifies the identity and implementation. The remaining precision tradeoff appears in benchmarks; a universal twofold wall-clock gain would still be unsupported.

A mixed-radix Gray traversal changes one coordinate at a time, allowing row values to be updated in `O(R)` coefficient-ring additions/scalings per transition rather than recomputed in `O(R times number_of_axes)`. Dense rows still generally require `R` ring multiplications per grid point. Sparse column updates can have additional structure, but should not be silently assumed.

Canonical creation-time representatives must be held fixed throughout the temporary higher-precision calculation. Nonunit division is done only after computing the numerator at the corresponding augmented precision, then dividing integer coordinates by the known power of two and inverting the odd factorial factor. The `R=0` empty-product case must be separate. Single active-axis cases have direct product shortcuts and are useful boundaries for both correctness and benchmarking.

## 6. Safe final claims

1. No packet in the inspected corpus supplies a complete measured fast SAT implementation or a proved stronger general logarithmic order.
2. A new kernel may establish an asymptotically smaller polynomial overhead per finite-difference grid and a measurable exact-subroutine speedup without changing the global exponential order.
3. Compare any new analytic contraction coefficient with compatible combinations, at least polynomial-space 66.6051 (the fixed-family 66.1927 infimum and the further two-stage 66.1205 boundary are sharper schedule comparisons) or more-memory time 44.5376/space 39.4960, as applicable.
4. Do not claim numerical dominance over the separate manuscript's unspecified constants, or over unproved conditional targets.
5. State resource tradeoffs explicitly, preserve the density envelope, and use normalized wire count `s` rather than silently replacing it by SAT-variable count `n`.
