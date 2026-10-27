> Historical initial-snapshot audit. The final fifteen-packet count and closing repository pin are established in `closing_source_audit.md`; that supplement supersedes the initial corpus count below.

# Audit of the complete current SAT frontier

Reviewed snapshot: `VladimirReshetnikov/ProveIt@ab2fbc9e03d5c3d0ad6dec8686960bfe498b0b06`.
There are **fourteen refinement packets and two primary manuscripts**. The topic README describes only the seven filed packets, not the seven new incoming archives added in `3e57705cf14ee9ac99c0ac35cfff751dcf70b396` (2026-10-27 01:54:16 UTC).

This audit checked every packet's README/status and relevant claim statements. It checked the slope-four decomposition, group locality, mode multiplicity, asymmetric scheduling, and proposed adaptive boundary schedule in detail. It did not rebuild the upstream formalization, prove all imported source theorems afresh, or execute a complete SAT solver. “Proved” below means a natural-language result relative to the explicitly imported contraction/reduction framework, not a new unconditional formal certification of ETH.

## Complete comparison

For numeric rows, the scale is `s/sqrt(log2 s)` in a base-two time exponent; `s` bounds Boolean wires and the normalized initial precision/truncation. Root degree is at most `ceil(s^0.9)` unless a stronger premise is expressly stated. Numeric network constants cannot be substituted directly for SAT-variable constants.

| Packet/manuscript | Strongest established result in this scope | Unproved target or restriction |
|---|---|---|
| OpenAI primary manuscript, vendored under `lib/openai-math/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/` | Appendix D: `poly(n,m) 2^{O_k(n loglog n/sqrt(log n))}`; fixed density `2^{O_{k,D}(n/sqrt(log n))}`; polynomial space | Upstream Lean scope advertises the weaker squared-loglog statement; no full rebuild in this task |
| Separate Claude `Research/claude-2o-n-3sat/eth.pdf` | Claimed `2^{O(min{km/sqrt(log m), k^2 n loglog n/sqrt(log n)})}` | Different architecture, no matched explicit leading coefficient; unpublished formalization cannot be independently rebuilt from this repository |
| `cauchy_mode_improvement` | Factorial Cauchy weights `1+b+2v2(b!)`, slope 3, `1/sqrt(3)` leading mode-entropy factor | No improved logarithmic order; kernel only |
| `eth_contraction_improvements` | Hermite leading precision 6 instead of 24; coefficient 648.4410666487529; streamed coefficient extraction uses at most `2^L` grid evaluations | No end-to-end solver or measured SAT speedup |
| `sat_density_improvement` | `poly_k(n,m) 2^{O_k((n/sqrt(log n)) min{log(2+m/n),loglog n})}` | General worst case and fixed density unchanged |
| `eth_density_refinement` | For `m<=Bn`, `B<=log(n)^A`, exponent `O(n log(2+B)/sqrt(log n))`; stronger local Smith evidence and matched constant refinements | Overlaps the preceding density result; unspecified general numeric network coefficient |
| `3sat_precision_refinement` | Leading Hermite precision 6; exact real taper minimax; local exact prototypes | `n loglog n/log n` (general) and `n/log n` (fixed density) need an unconstructed structured-mode summation algorithm |
| `3sat_refinement` | Scalar parity lift, surviving incidence degree `k(p+a-1)`, eliminating auxiliary coefficient axis | `n (loglog n)^(3/2)/log n` needs a missing compact factorization |
| `3sat_asymptotic_analysis` | Scoped barriers; no stronger general asymptotic bound | `n sqrt(loglog n/log n)` and `n/sqrt(log n)` need missing recursive/compression interfaces |
| Incoming `eth_balanced_packing_2026-10-26.zip` | Coefficient 94.74820225953412; balanced pair loads, additive precision guard | Polynomial space; no improved logarithmic order |
| Incoming `eth_high_moment_2026-10-26.zip` | Coefficient 94.74820225953414; higher-moment labeling; alternative 98.89670023224618 | Lower-degree specializations 42.3726842 and 31.2364960 have stronger input assumptions |
| Incoming `eth_packet_refinement_2026-10-26.zip` | Coefficient `9*pi*sqrt(22)/(2*ln 2)=95.6639404728982` | Polynomial space; no improved logarithmic order |
| Incoming `eth_recursive_refinement_2026-10-26.zip` | Coefficient 133.20737249245013; actual-domain Cauchy slope `64/21` | Low-degree 60.70695755 is a different premise; finite inventories can favor older basis |
| Incoming `3sat_round2_refinement_20261027.zip` | Coefficient 84.06627149423657; safe eventual coefficient 85 | Polynomial space; no improved logarithmic order |
| Incoming `eth_asymmetric_packet_balancing_2026-10-26.zip` | Coefficient `pi*sqrt(5/2)*(9+sqrt(3))/ln 2 = 76.90899495160009` | Low-degree 31.06413206299 requires maximum degree `s^(1/12)`; fixed-r boundary infimum 76.4327736858 is not its displayed certificate |
| Incoming `eth_joint_cauchy_2026-10-26.zip` | Full-orientation weights `a+1-i+4q-2popcount(q)` at all retained levels, same family multiplicity. Its own polynomial-space coefficient 319.6857570777 | Its optional table/matrix route has time 225.5970572839 and **exponential-space** coefficient 196.1994455176; it is a separate resource tradeoff |

All seven new incoming reports compare against the older seven packets. They do not compare their new ingredients against each other. Therefore 76.90899 is the strongest displayed same-interface polynomial-space certificate, but it is **not** the strongest readily composable baseline.

## Correct composable baseline

Combine the full-orientation slope-four basis from `eth_joint_cauchy` with the asymmetric schedule from `eth_asymmetric_packet_balancing`. The latter has at most

`c_i = (2(1-1/r)+o(1)) M/D_i`

mode families, precision `(6+o(1)) M D_i/u`, and child ratio `(2/r+o(1))`. The former has `2^i` modes of each q per orientation and two orientations per unequal-symbol packet. Thus **the family count, child graph, and fresh-side degree bound do not change**. Its source linear form reads a whole half-packet, but that half-packet lies in one source group; the target lies in one other group. Packet entry cost remains `exp(O(L log s))`, or the earlier streamed variant.

The slope-four partition free energy is `pi^2/(24 theta)+O(log^2(2/theta))`. The local natural-log coefficient is consequently

`kappa_r = pi sqrt(2(1-1/r))`,

instead of the slope-three value `pi sqrt((8/3)(1-1/r))`.

At r=16 with the existing explicit schedule `u0=floor(lambda/81)`, `u_d=floor(lambda/(108*4^(d-1)))`, the path factor is `9+sqrt(3)`. The **composed existing-ingredient baseline** is therefore

`C_comp = pi sqrt(15/8)(9+sqrt(3))/ln 2 = 66.60514340761482`.

It would overstate the contribution to advertise this alone as inventing a new mode basis or packing lemma. It is a useful checked synthesis beyond the individual displayed constants. To exceed the strongest compatible envelope, compare a further improvement against this synthesis (and, where relevant, its limiting schedule value below).

## Exact adaptive boundary schedule

The excluded fixed-parameter boundary in the asymmetric report can be reached as a `(C+o(1))` theorem by approaching it slowly enough to absorb all logarithmic buffers. Define

```
lambda = ceil(log2 s)
g = ceil(sqrt(lambda))
B = floor((lambda-g)/80)
b = ceil(6 log2 lambda)
u_0 = B
u_d = floor(3B/4^d), d>=1
a_d = sum_{j=0}^d u_j + (d+1)b
r = 16, Q_d = 16^a_d, L_d=2^a_d
H = ceil(s/lambda)
```

For bounded sizes where a parameter is inadmissible, use exhaustive contraction. This changes no asymptotic conclusion.

Prove applicability first for every hypothetical active depth `d<=d_* = ceil(log_6 lambda)+2` and `M>H`. Since `sum_{d>=1} 3B/4^d = B`,

`a_d <= 2B + O((log lambda)^2)`.

Uniformly in that range,

`u_d >= lambda^{1-log_6(4)+o(1)}`,

so all floors have uniformly vanishing relative effect. Here `1-log_6(4)>0`.

At the root, `R=C=Delta=ceil(s^0.9)`, and

`Q_0^2 Delta lambda^2/M <= 2^{-g/10+O(log lambda)} = o(1)`.

The other root padding terms are smaller. Below the root, retain original tensors on the row side, giving `R_d<=Delta`; fresh packet tensors give `C_d<=2 L_(d-1)`. Hence

`Q_d R_d/M <= 2^{-g/10+O((log lambda)^2)} = o(1)`,

while both `Q_d^2 C_d lambda^2/M` and `L_d Q_d^2/M` are bounded by

`2^{-31 lambda/40+o(lambda)}`.

New packet degree is at most `s^(1/40+o(1))`, so stays below Delta. These estimates prove uniform `(1+o(1))` padding; eventually every child has at most `M/6` wires. The bootstrap therefore validates the hypothetical depth range. More sharply `M_d <= s ((1+delta_s)/8)^d`, with `delta_s -> 0`.

The existing additive-buffer precision proof applies unchanged: `D_i>=2^(a_(d-1)+b+1)` and inherited precision `p=O(s lambda^2 2^a_(d-1))` imply `p/(M D_i/u_d)=O(lambda^4/2^b)=o(1)`. Packet, entry, precision, graph and interpolation costs remain polynomial or subdominant as in the asymmetric paper.

The path sum is

`sum_d M_d/sqrt(u_d) <= (sqrt(80)(1+1/(3sqrt(3)))+o(1)) s/sqrt(lambda)`.

Thus the slope-four composed adaptive certificate is

`C_boundary = pi sqrt(150)(1+1/(3sqrt(3)))/ln 2 = 66.19272369357722`.

No incompatibility has been found in this argument. It certifies a limit coefficient with a vanishing correction; it does not claim that the finite-size factor is <=2^(C_boundary*s/sqrt(log2 s)) with no correction, and it gives no useful practical crossover.

## Scope qualifications needed for the final report

1. The conditional `n/log n`-type targets are not algorithms and cannot enter a proved upper-envelope comparison. Their missing interfaces remain open.
2. The separate Claude manuscript leaves the matched network constant unspecified. A lower numeric contraction constant cannot prove a numeric runtime domination over that different algorithm. Likewise, uninstantiated big-O constants cannot be totally ordered numerically.
3. Preserve the strongest density-sensitive envelope. For extremely few clauses, remove unused variables first and multiply the count by the appropriate power of two; with active variable count N<=min(n,km), compare bounds in N. This also accounts for the clause-count branch of the alternate manuscript at the level of order, subject to fixed-k constants.
4. Low-degree constants, including 31.06413, must be compared under their smaller-degree premises. A new 66-level general certificate is not worse than those specializations; it covers a wider input class. An envelope implementation can retain all existing specialization branches.
5. No local kernel timing measures SAT solving. Any practical performance claim must name the kernel, precision, instances, and matched implementation baseline.
6. The old density packet's local slope-four Smith spectrum is prior work; the joint packet supplies the crucial constructive all-level full-orientation locality without extra families. Credit that distinction accurately.
7. Substituting normalized wire constants directly for n is unjustified until the reduction's wire constants and additional branching costs are tracked.

## Exact detailed source anchors

- Asymmetric report: `thm:pair-balance`; `cor:padding`; `eq:padding-conditions`; `eq:family-count`; `lem:side-degree`; `eq:sharp-precision`; `eq:main-schedule`; Appendix `app:optimization`.
- Joint-Cauchy report: `lem:separation`; `lem:valuation`; `thm:modes`; `cor:smith`; section `sec:compatibility`; `eq:colors`; `eq:budget`; exact arithmetic subsection; mode entropy section.
- Prior precision packet: `notes/conditional_theorem_review.md` explicitly states the unconstructed acceleration hypothesis and the retuning required in the SAT reduction.
- Prior barrier packet: `research_decision/findings.md` carefully scopes the support-entropy and taper barriers and the missing coefficient/low-wire interfaces.
