# Supplemental exclusion audit: packet 2026-10-26v

## Decision and exact scope

**All six retained directions A–F survive comparison with packet v. No additional overlap requires withdrawing a direction.** This is a bounded claim about the inspected proposal corpus, not a claim of worldwide mathematical novelty.

This addendum supplements, without replacing or modifying, the original audit of 21 packets a–u at tested source commit `29936089835c0c55cca81edc86b4fb0c70ce34d5`. Packet v was discovered in the later repository state `45ac0dfc366f798d4686070a89d66e8dafdb6879`. The compiler-validation pin remains `29936089835c0c55cca81edc86b4fb0c70ce34d5`; this supplemental reading does not claim compilation of the later dependency tree.

Packet location: `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26v/`. Its own reviewed source is `22e020937caa81d0cb72a4f63071d6c0bcc1eba9`. Its placement notice records arrival through `docs/incoming/ProveIt_Lean_Simplification_Round3_2026-10-26.zip` at commit `74c3273be4`. The notice records 985 archive members, 107 placed members, and 878 omitted byte-identical source/baseline members. The actual Git subtree has **109 file entries**, including placement metadata. These are different counts and are not silently combined.

The audit read the complete substantive TeX manuscript (all ten sections and the wrapper), the independent and final report reviews, local mechanism reviews, novelty decisions, all standalone candidate Lean files, the complete proposed state-encoding module, and all five placed integration patches. The 29 selected files total 92,189 bytes. Their SHA-256 digests and verified Git blob identities are recorded in `late-packet-v-manifest.json`, alongside the complete 109-path Git tree inventory. This was selective Git-object reading: irrelevant binaries, duplicated baseline snapshots, and all omitted archive members were not re-downloaded. The packet's PDF was not re-rendered in this audit. No packet code or reproduction script was executed.

## Mechanisms that must now be treated as already applied

Paths below are relative to packet v. Optional and uncompiled proposals count as exclusions.

| Packet item | Exact proposed mechanism | Source anchors |
|---|---|---|
| E1 | Identify the existing terminal-state encoder with `Fin.val` after `finSuccEquivLast.symm`; derive injectivity by composition. Preserve `none = 215` and `some q = q.val`. | `report/sections/04_encoding_action.tex:3`; `encoding/StateNumberCandidate.lean:13–19`; `encoding/StateNumber.patch` |
| M1 | Rewrite action halt equality through `stateNumber_injective.eq_iff`, `act_stateNumber`, and `stateNumber_none`. Retain the target-below-216 premise. | `report/sections/04_encoding_action.tex:23`; `machine/MachineCandidates.lean:16–18`; `machine/M1-act_next_none_iff.patch` |
| M2 | Prove the unchanged three-way color-action formula by splitting only on the old head/write site, leaving the new-head conditional symbolic. | `report/sections/05_machine.tex:3`; `machine/MachineCandidates.lean:20–30`; `machine/M2-color_action.patch` |
| M3 | Replace the sign split converting a sharp trace exterior condition by `le_abs'.mp`. | `report/sections/05_machine.tex:18`; `machine/MachineCandidates.lean:32–34` |
| R1 | Translate by the seed and use guarded `Int.induction_on` for propagation over an open interval. Both strict bounds remain in the induction motive. | `report/sections/06_interval.tex:1`; `rows/IntervalPropagationCandidate.lean:12–34`; `rows/WangTiles942ResetRows.lean.patch` |
| R2 | Define a signal at the left endpoint of the moved-head bond; prove west/east formulas jointly, then horizontal compatibility by translation. | `report/sections/07_pulse.tex:1`; `rows/BondPulseCandidate.lean:16–48`; `rows/WangTiles942StepConstruction.lean.patch` |
| Notes-only | Derive `step_head_ne` directly from `step_eq` and `moved_head_ne`. The packet does not count this clarity variant as a saving, but it is still prior proposed work. | `machine/MACHINE_REVIEW.md:81–83`; `baseline_audit/NOVELTY_DECISIONS.md:89–94` |

M3, R1, and the shared-edge content of R2 were already within the exclusion boundary established by packet u: its report's trace conversion at lines 440–448, centered integer interval propagation at 270–318, and shared-edge Wang construction at 353–438. Packet v therefore enlarges the inspected corpus without making those mechanisms newly available to recommend. Its own novelty decisions were made against an earlier assumed-applied baseline; those decisions are not substituted for our 22-packet comparison.

The packet explicitly labels every new Lean candidate **uncompiled**. Its independent review checks mathematical contracts and source preservation, and its final review checks report consistency/layout. Neither is a Lean elaboration result. Their presence is sufficient to establish prior advertised ideas; compilation is not a condition for exclusion.

## Comparison with the six retained directions

### A — WangTiles942HelicalQuotient.row_zero_of_helix

**Retain.** The retained proof makes a diagonal orbit period one and consumes the integer-multiple periodicity API. R1 retains guarded Int.induction_on for an open interval; R2 derives translated horizontal edge fields from tile constructors. Neither states a helix-orbit periodicity adapter or removes the signed helix induction by periodicity.

### B — RatioReparameterization.combined_dvd_iff

**Retain.** Coprime extraction and cancellation for J*F dividing Q*F+J*T is a divisibility theorem. M1 reflects equality through the finite machine-state encoder. The shared word cancellation does not identify the obligation or adapter.

### C — PolynomialRangeBounds.geometric_identity; geometric_lt_two_top

**Retain.** The retained client uses the geometric-series multiplication identity and derives its inequality without a second induction. Standard-library reuse in E1 and M3 advertises specific finite-state and absolute-value clients, not this finite-sum algebra.

### D — MarginSeparation.coordinate_gt_of_margin_pos

**Retain.** The retained argument derives an open interval from a positive quadratic margin and a square comparison. M3 uses le_abs' to reflect an exterior condition into a disjunction for a machine trace. It provides no square-window interval lemma or margin client.

### E — SparseBorrowCarry signed finite-prefix divmod interface

**Retain.** The retained optional interface identifies final borrow with Euclidean quotient of the signed prefix and normalized word with remainder, including negative prefixes. Packet v contains no borrow, finite signed prefix, quotient/remainder, or radix-normalization proposal.

### F — NativeRankVariation fixed-parameter comparison through C+q*F

**Retain.** The retained optional interface factors actual rank order/equality through C+q*F at fixed ports, q and J, and q>1. Packet v concerns machine colors and row construction, and contains no scalar rank comparison or rank-potential theorem.

## Boundaries and remaining claims

For E, the finite endpoint decomposition is signed Euclidean division by positive `B^n`, including negative raw prefixes and the empty prefix. This is not a new adoption of packet v's finite-state equivalence, and no periodic/cyclic carry conclusion is claimed.

For F, fixed ports, `q`, and `J` are material. The interface identifies ordering and equality through one scalar and does not claim injectivity of the pair `(C,F)`, a safe mutation of arbitrary machine states, a controller certificate, or a new magnitude envelope. The earlier packet-u rank envelope remains excluded.

The direct A–D patches and optional E–F adapters therefore keep their previously reviewed status. This addendum adds an exclusion receipt only; it does not add line savings, compile packet v, expand the verified dependency tree, or retroactively alter the original 21-packet corpus manifest.
