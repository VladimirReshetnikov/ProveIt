# Late closing-snapshot review: frontier and contraction-tree packets

Closing cutoff: `fa6e904d109b738154db7fe41e7f2777e6d24aee` (as supplied by parent). Reviewed only static README, report TeX/fragments, and relevant implementation source. No archive-provided code executed. This addendum supersedes novelty/comparison statements in the earlier packing review wherever they conflict.

## Immediate consequences for our deliverable

1. **Multi-depth adaptive alphabets are already present** in late `subexponential_sat_frontier_2026-10-26.zip`. Its polynomial-space coefficient is63.85220339055; ours63.75899407489 is modestly smaller, but we must claim improved explicit allocation, not introduction of the multi-depth scheduling idea.
2. **Cached time35.35458805840 is now supplied** by `subsat_contraction_tree_2026-10-26.zip`, with space34.27480300502. Our earlier37.5917 cached coefficient is not the smallest time upper bound. The old option may retain a lower memory coefficient; treat a resource frontier, not a scalar rank. New tree/field-backend components are compatible with our schedules, subject to recomputing the full recursive maximum.
3. **Prefix Cauchy feature reuse is already supplied** in the contraction-tree packet: O(L+PB²) becomes O(L+PB), same precision and constant per-port auxiliary storage. Our independently derived Cauchy recurrence is now a reproduction/implementation verification, not a novel asymptotic kernel improvement.
4. **Dense quadratic balancing is already supplied** by the frontier packet: O(NQ³) becomes O(NQ²), exactly preserving scores and returned certificates. Our sparse positive-support delta and first-absent-label shortcut are not present in its inspected implementation. Claims should compare sparse scoring against this stronger dense baseline, not only cubic rescoring.

## `subexponential_sat_frontier_2026-10-26.zip`

### Mathematical frontier

The archive reviews15 prior packets and pins474ddba696a5d385c091c23fb2995f69edd13e00. `theory.tex`, equation `eq:ps-schedule`, uses alphabets13,14,8,6, then4 forever. Retained fractions are27/2000,51/4000,141/20000,107/20000, followed by(27/6400)(5/8)^k. Cumulative limits: .0135,.02625,.0333,.03865,.0499. These are almost the same early regimes as our new schedule, so novelty must be narrowed.

Theorem/constant `eq:ps-constant`:
`C_ps=63.85220339055...`, polynomial space, same normalized <=s wires / maxdegree<=ceil(s^.9) / initial-entry and precision interface. Static proof has correct side-specific root/nonroot gates, fresh-side/rounding bounds, and noncircular depth bootstrap; geometric tail ratio sqrt(2/5) is strictly<1. It compares not only asym fixed16 coefficient66.60514 but also fixed16 boundary66.19272 and root17/tail13 boundary66.12047546. Thus those comparisons were already explicitly available by closing cutoff.

Its cached schedule is root7/tail9, retained root89/5000 and tail(1233/125000)(7/25)^(d−1), total capacity63/2000. Root block construction dominates its root Strassen multiplication, and the full descendant recurrence dominates the root local term:
- root local37.59170256;
- complete time37.93010908288;
- space33.62304092166.
The report correctly includes child-oracle calls, table building and sequential-record access. A critical warning is explicit: reporting only the root local37.5917 for that exact tail9 schedule would be wrong. Our distinct tail schedule must retain its independently checked recurrence.

It also identifies the stronger retuned old fixed-r8 boundary time38.1677456970 / space33.9927010637; fixed16's44.53757 is not the appropriate strongest old cache baseline.

### Balancing implementation

`code/cached_balancing.py` uses future products plus maintained cell powers and row sums. At each column, `base=sum_a F'_a S_a`, `coeff_a=F'_a(q^w−1)`, `score_b=base+sum_a coeff_a q^load_ab`. It materializes/scans allQ scores and allQ rows, including zero weights/cells. Exact averaging and final cache invariants are checked. This is a proper O(NQ²) reference, not sparse positive-support scoring.

Our sparse identity subtracts the label-independent `sum_a coeff_a`, scoring only `coeff_a(q^load_ab−1)`, and exploits positivity to choose first missing label. That extra observation and support-sensitive operation count survive this particular late source. Our benchmark's independently authored dense-delta comparator already provides the essential stronger comparison, but the attribution and headline must be updated.

### Precision peeling

`implementation.tex`, `thm:peeling`, factors guaranteed target valuation V(beta) out of every mode contribution, computes normalized children at Q=P−V, and restores2^V modulo2^P. Each mode has one target, so per-group valuations add exactly toV. Division is performed using c modulo2^(Q+w), with Q+w<=P for every used mode; no illegal division of an already low-precision residue is used. Retained tensors are newly capped/frozen atQ and nested caps flatten to the minimum. For cached contraction, exact-weight arrays fixV, so one array uses a common residual ring. Static algebraic proof is coherent. This is another existing compatible component to retain, not claim as new if independently rediscovered.

Reported finite counts and timings (840 complete certificates, precision-peeling fixtures etc.) are archive evidence only, not reproduced in this static review.

## `subsat_contraction_tree_2026-10-26.zip`

### Main theorem

`report/cached_tree.tex`, theorem `thm:cached-tree`, gives
`C_T=pi sqrt(24339)/(20 ln2)=35.354588058401...`,
`C_S=pi sqrt(915)/(4 ln2)=34.274803005023...`.
Same generic high-degree normalized interface; subexponential space, no polynomial-space claim. It imports upstream exact contraction, asymmetric balancing and slope-four modes.

New backend/table components:
- Weighted pair entropy on scaleK=pi sqrt2/ln2 *M/sqrtu with coefficient sqrt(sum_e z_e²)/r.
- Cache singleton group functions, charging all recursive child contractions (2(r−1) incident directed pairs each).
- Build a block table by binary merges rather than flat internal-index enumeration. For subset split sizesa,b, k=a+b, reshape into matrix dimensions whose pair-class cardinalities are2a(r−k),2ab,2b(r−k). This factorization is exact: only A–B indices are shared, while external A/outside and B/outside index collections are disjoint.
- Multiply via exponent12/5 field backend, bridged to the actual ring through integer module coordinates and CRT. Worst weighted exponent uses weights1,1,2/5, giving discounted cardinality `sum(v)−(21/25)min(v)`.

The integer-coordinate bridge appears internally coherent: fixed rational bilinear algorithm, fixed exceptional-prime set, polynomially many small nonexceptional odd primes whose product exceeds the polynomial-bit reconstruction bound; coordinate products are ordinary bounded nonnegative integer matrices; combine structure constants and reduce mod2^p. Only unit inverses in auxiliary prime fields are used. Polynomially many module-coordinate pairs and primes add polynomial overhead; sequential fixed-base multiplication has quadratic element storage. The code does not implement the asymptotically fast backend, as explicitly disclosed.

External support checked via the primary arXiv abstract: [More Asymmetry Yields Faster Matrix Multiplication](https://arxiv.org/abs/2404.16349) states an exponent strictly below2.4 (current page reports2.371177). The late packet deliberately needs only strict<12/5, not a current-record claim. This check supports the imported field-exponent premise; it is not a full independent audit of the underlying fast matrix theorem.

Exact table ledger from static arithmetic:
- r8, blocks3,3,2: cache14, maximum merge766/25, triangle798/25, memory boundary30 (all divided by r² then square-rooted).
- r12, blocks4,4,4: cache22, max merge1632/25, triangle1728/25, memory boundary64.
These values correctly follow the displayed cardinality formulas; triangle dominates construction in both.

Schedule: rootr8,u0=lambda/61; tailr12,ud=125lambda/(13176*6^(d−1)); total retained capacity1/36. Leaf cutoff is s/lambda^(3/4), not s/lambda. That adjustment matters: it makes active taper lengths diverge despite decay6 and tail child shrink1/6. Coarse shrink1/5 and exponent `1−3ln6/(4ln5)>0` close the hypothetical-depth argument. Root symmetric exponent609/610 and tail row gate.9+log2(12)/36<1 have fixed margins; fresh/rounding gates are far lower. Added logarithmic buffers and precision inheritance are paid.

Full recurrence has root-local35.354588 and descendant candidate34.812362, so root dominates. Space uses maximum of ancestor/descendant table coefficients, not sum; root34.274803 dominates tail10.967937. These comparisons appear coherent on static inspection. No gap was found that would justify ignoring this better supplied time bound.

### Cauchy prefix overlap

`report/prefix_theorem.tex` gives the exact streaming recurrence for normalized plus/minus full-orientation features. It stores each product as exact2-adic valuation plus unit modulo2^p, cancels denominators before modular reduction, handles zero products explicitly and stops after portj. This yields O(L+PB) operations and unit inversions, rather than O(L+PB²), at fixed precision with O(1) auxiliary ring elements per port. This directly overlaps our recurrence's theoretical novelty. Our complete denominator-table caching might still offer an independently measurable additional operation reduction, but that requires a fair comparison with this prefix implementation; merely comparing against direct products is no longer enough.

Archive benchmark numbers are not rerun or independently validated. The supplied statement itself properly limits them to kernels, not SAT runtime.

## Closing recommendation

Retain all valid inherited components, revise attribution and comparisons, and lead with only improvements that remain after this closing snapshot: a genuinely smaller explicit schedule where established, the sparse-support balancing step if the other late packets do not already contain it, and independently verified refinements to the new strongest backends. Do not claim all-source numerical dominance by comparing only against the earlier asymmetric76.909 or cached44.538 numbers.
