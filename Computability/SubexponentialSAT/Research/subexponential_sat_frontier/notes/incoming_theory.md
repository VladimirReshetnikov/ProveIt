# Incoming theory review and combined upper-bound inventory

Snapshot: ProveIt `ab2fbc9e03d5c3d0ad6dec8686960bfe498b0b06`.
All paths below are inside the extracted incoming archives.

## Reviewed four archives

| Archive | Main result on generic normalized interface | Actual method and parameters | Scope/limitations |
|---|---:|---|---|
| `eth_asymmetric_packet_balancing_2026-10-26.zip` | PS coefficient 76.90899495160009 | Exact rational two-stage vertex labeling; root both sides degree s^.9, descendants retained side degree s^.9 and fresh side degree 2L_previous; r=16, u0=lambda/81, u_d=lambda/(108*4^(d-1)) for d>=1; additive6log lambda buffer; exact unequal-symbol fraction and factorial slope3 | Strongest of these four for the full generic interface. Full theorem retains upstream deformation/recovery/factorization. Low-degree31.06413206 needs degree<=s^(1/12). Annulus-mode slopes4,16/5,64/21,... tend to3 and do not improve the uniform slope. |
| `eth_balanced_packing_2026-10-26.zip` | PS coefficient94.74820225953412 | Same symmetric pair-load capacity as high moments but achieved in polynomial time by greedy row labeling and exact column exponential potential; r=54, asymptotic u_d=[2/(45log2 54)]lambda/9^d; adaptive integer capacity approaches strict boundary safely | No asymmetry invariant used in scheduling; all modes charged2M/D instead of exact2(1-1/r)M/D. Stronger than its fixed rational94.75370150 schedule. Low-degree interface separate. |
| `eth_high_moment_2026-10-26.zip` | PS coefficient94.74820225953414 | Moment potential sum_gamma(X_gamma-mu)^(2t); t=lambda; r=54, same asymptotic retained-range fractions and capacity as balanced; growing moment construction costs exp(O(lambda²)) and polynomial space | Setup is quasipolynomial time, correctly charged lower-order. Fixed moment t gives coefficient times sqrt((t+1)/t) with polynomial setup. Separate polynomial orbit-padding certificate98.89670023. Degree-sensitive42.3726842 and bounded-degree31.2364960 use stronger input assumptions. |
| `eth_recursive_refinement_2026-10-26.zip` | PS coefficient133.20737249245013 | Retains original second-moment packing algorithm but removes crude factor3 from its asymptotic padded-mass estimate; r=54, u_d=lambda/(260*9^d); additive squared-log precision gap; genuine group-preserving residue-aware Cauchy weights of uniform slope64/21 | Same schedule with slope3 gives134.2604115868. Finite weights are not pointwise stronger; the report records all21 tiny sampled inventories favoring the older basis. New basis becomes asymptotically better. Its sparse-query lower-degree60.70696 specialization is not generic. |

All four explicitly distinguish mathematical upper-bound coefficients from
measured SAT runtimes. None contains an end-to-end SAT solver or a new Lean
certificate. Their full counting consequence depends on unchanged upstream
algebraic identities and reductions. I found no concrete defect in the
audited new local lemmas, but did not independently formalize the source or
execute all four archived test suites. New schedule checkers were executed.

## Mathematical audit details

Asymmetric report anchors (`.../report.tex`): pair-load theorem311-381;
near-lossless packing gates383-400; exact unequal-symbol count438-442;
fresh-side invariant447-461; additive precision estimate495-529; factorial
entropy532-559; fixed schedule563-569; parameter bootstrap575-619;
full cost621-663; low-degree specialization813-847; boundary optimization
857-892. Its boundary coefficient76.4327736858 is expressly an infimum,
not its displayed fixed-parameter theorem.

The pair-load proof is sound at the inspected level: greedy whole-row
assignment bounds W_a<=M/Q+R, exponential conditional expectation gives
the column bound with C, and all rational intermediate values have polynomial
bit length. The descendant orientation preserves all old vertices on one
side and all new packet tensors on the other. This asymmetry can be used
again at every later call.

High-moment report153-209 handles multiedges via a matching partition with
K<=2Delta-1, Holder's inequality, an exponential moment estimate, and an
even centered-power potential. The explicit expansion correctly tracks at
most4t unassigned endpoints and a common rational denominator. Its stated
growing-t complexity is exp(O(lambda²)), not polynomial, and the full proof
pays for it. Orbit padding247-291 controls total orbital rounding separately;
it does not evade the current common-padding degree bottleneck.

Recursive report's exact Hermite precision is near310-333; original
second-moment sharp packing338-375; schedule377-393; entropy and main theorem
490-545. The actual alphabet is54, not64. Kernel file260-276 establishes
the64/21 asymptotic slope and retains each source/target group. This makes
it compatible with asymmetric scheduling, although the joint packet's later
uniform slope4 gives a stronger current composition.

## Other incoming components used for combination

The joint-Cauchy report's all-level, whole-orientation basis has slope4 at
the same family multiplicity. Its optional exact pair-weight indexing,
group caching, three-block tables, and division-free rectangular Strassen
algorithm are a different time-space regime. Its printed225.59705728 time
and196.19944552 space coefficients used old threefold packing and r=256.
Reusing these coefficients without replacing the packing/schedule would miss
the strongest combined baseline.

The round-2 archive `report/combined.tex` ALREADY varies the alphabet by
depth: root r0=37, u0=(10/1043)lambda; tail r=8,
u_d=lambda/[236*(5/2)^(d-1)]. It has polynomial-space coefficient
84.06627149423657 with factorial slope3, and counts exact crossing pairs.
It does not use the asymmetric fresh-side degree improvement. Its mathematical
claim that changing root/tail alphabets is possible is prior art within this
corpus. Our novelty is a better explicit multi-stage/cached allocation, not
the fact that alphabets may change.

The packet-refinement archive has r=54, u_d=lambda/(132*9^d), explicit
coefficient95.6639404728982 with slope3; it also optimizes the symmetric
family to boundary94.7482022595 at r=54. Neither beats asymmetric scheduling
after applying the same compatible mode and caching refinements.

## Polynomial-space combined comparison

All numbers below use the full degree<=s^.9 normalized interface. A lower
coefficient under a smaller-degree assumption is not a competing theorem
for every such input. Retain those specializations in a portfolio.

| Construction/composition | Coefficient on s/sqrt(log2 s) | Status |
|---|---:|---|
| Balanced/high-moment reported |94.7482022595| Prior theorem, slope3 |
| Same with full-Cauchy slope4 |82.0543501197| Compatible prior composition; could additionally retain crossing savings |
| Packet-refinement with slope4 |82.8474026757| Compatible prior composition |
| Recursive schedule with slope4 |116.2729271567| Replace64/21 by4; weaker schedule |
| Round-2 root37/tail8 with slope4 |72.8035267154| Compatible prior composition |
| Asymmetric fixed-r16 with slope4 |66.6051434076| Strongest simple composition of displayed generic PS schedules |
| Asymmetric fixed-r16 boundary with slope4 |66.1927236936| Stronger prior-family envelope; not fixed equality theorem |
| Root17/tail13 continuous two-stage capacity allocation |66.1204754600| Additional numerically chosen comparison from prior general structures; not global optimum claim |
| New explicit13,14,8,6,4,4,... rational schedule |63.8522033905| New strict-capacity theorem; exact interval checker |

The new coefficient improves66.605 by4.133224%,66.1927 by3.535918%, and
the further66.1205 comparison by3.430514%. These are coefficient reductions,
not wall-clock speedups or lower bounds on previous implementations.

## Cached/Strassen comparisons

For near-unit packing and slope4 use

    K(M,u)=(pi sqrt2/ln2)M/sqrtu.

For r groups and three blocks, group-cache entropy is
a_r=sqrt(2(r-1))/r. Table-build entropy is the maximum of
sqrt(2rk-k²-k)/r over block sizes k. Block memory is
max sqrt(2k(r-k))/r. The Strassen coefficient discounts the smallest
directed block-pair class by1-(log2 7-2)². Always take the MAXIMUM of
table-build and Strassen coefficients; at r7 table construction wins.

The following straightforward compositions have root matrix/table work
dominating their complete cached recurrence; tail work was checked against
the cached-child geometric sum.

| Prior schedule + near-unit packing/full-Cauchy/cache | Time coefficient | Space coefficient |
|---|---:|---:|
| Asymmetric fixed-r16 (u0=1/81) |44.5375718550|39.4959495337|
| Its fixed-r16 boundary (u0=1/80) |44.2617947647|39.2513902192|
| Asymmetric symmetric comparison r48,u0=1/128 |55.6686025848|48.3451748462|
| Balanced/high moment r54 |55.9905860208|48.6248000709|
| Packet-refinement r54,u0=1/132 |56.5317331664|49.0947571411|
| Recursive r54,u0=1/260 |79.3399657710|68.9024753521|
| Round-2 root37/tail8 |50.4062312620|44.1948978541|

More importantly, retuning the already-described fixed-r asymmetric family
for cached cost gives the stronger r8 capacity-boundary comparison

    time38.16774569701537, space33.99270106370396.

The new strict rational root7/tail9 schedule gives

    time37.93010908288456, space33.62304092165775,

improving the time coefficient by.622611% even against that stronger
comparison. The exact checker proves eventual integer coefficients38 and34.
It is not justified to call38.1677 an optimum over all possible schedules;
it is a specific strong prior-family envelope used conservatively here.

## New artifacts and independent review

`analysis/theory/heterogeneous_schedule_proof.md` contains the full
polynomial-space proof. `verify_heterogeneous_schedule.py` certifies exact
integer power gates and rational enclosures of the constant.

`analysis/theory/cached_schedule_proof.md` contains exact7/9 pair counts,
resource recurrence, parameter bootstrap, time and space proof.
`verify_cached_schedule.py` imports its interval arithmetic from the PS
checker and independently certifies the cache/table and tail inequalities.
Both run identically under normal and optimized Python; the paired JSON
files were compared byte-for-byte.

The baseline-audit agent independently checked compatibility of variable
alphabets, all PS capacities, shrink products, entropy normalization and
bootstrap and found no defect. Its separate cached audit identified the
root7 table-build term exceeding Strassen; the same inequality was caught
by the exact checker, and the corrected result still has total time
37.930109 because root-cache plus first-tail work dominates.

No claim is made over the separate49-page algorithm's unspecified leading
constant. No stronger unrestricted SAT logarithmic order, unprovedn/logn
interface, or independent verification of the full upstream formalization
is established by these new schedule calculations.
