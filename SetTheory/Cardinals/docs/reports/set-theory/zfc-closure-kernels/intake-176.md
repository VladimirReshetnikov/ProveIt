# Intake 176: two more 236-state packages

Placement `0af33e8d0b` imports two packages as **Sources 113–114** and retires their
ZIPs. The host now reconciles **114 sources**; the collection remains **290 reports**.
The [placement map](data/intake176-placement.json) accounts for all 416 members: 218
staged byte-identical (0 mismatches against a fresh extraction), 192 exact aliases and
6 archive-only.

The canonical census finds **no table below 236**. Both packages carry Source 112's
236-state machine (canonical `d4302309…`), published as
[`candidate-rotated236`](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-rotated236/README.md).

## Source 113 — `ZFC236_Audit_and_Quantifier_Bootstrap_2026-10-19.zip` (prefix `113-aud236-`)

Arrival `b272323b09`. It audits the 236 and credits its construction to Source 112.
The audit covers the source reassociation, the literal table, the 409,835-step
startup, a separate four-case fold proof, and a fresh unbounded runtime proof
(2,267,815 rules) whose case array matches the incoming one exactly. Its new results:

- **E667.** The 692-bit packet E692 already forces its designated constant to be
  Boolean truth, so its explicit truth equation can go: 25 bits saved, with seven
  equations and nine symbols. It has the same models and ground-query consequences as
  E692, and the same inherited calibration (non-derivability of `N(d,d) = d`). No
  state count.
- **Logical basis.** Keep the other numerical-calculus rows and the gated CP/GIC
  bundle. Then the schema `Q_i A → Q_i Q_i A` recovers double-negation elimination for
  every numerical code, code 0 included. K/S with global DNE equals the old numerical
  theorem calculus. Twelve finite Hilbert certificates contain 2,015 checked proof
  nodes.
- **Exact source costs** of these logical variants, best of 288 each: K/S/Peirce 226
  shared nodes; K/S/Q4, K/S/quantified-DNE and K/S/DNE 227; the original is 224.
  Adding the six-leaf NIP specialization does not improve them. These are source costs,
  not state counts. By the decoder accounting of [intake 175](intake-175.md), they are
  2–3 nodes *worse*.
- **970 affine register-offset invariants.** A primal discovery is paired with an
  independent dual checker. The invariants transfer to the 236 source because its
  guarded control-flow graph is unchanged. No smaller machine follows from them yet.
- **Scoped searches.** Expanded helper, caller-encoding and halt-aware classes on the
  237, and a targeted eight-pair search on the 236, found no new table. No lower bound
  is claimed.

## Source 114 — `ZFC236_Reassociation_2026-10-19.zip` (prefix `114-reas236-`)

Arrival `b7d3e41404`. It **independently constructs the same 236-state table**: the same
closed reassociation at source prefix `1110100100110110101010011100001` (chunks of 245, 160
and 132 leaves), the same seven retained-row changes and the same deletion of 223. It
supplies its own certificates: the source graph (6,455 leaves; 8,385 non-halting edges
and one halt), a replay of Source 103's 13 stages, the all-tape fold with clock
`τ(t) = t + 2A(t)` and `t ≤ τ(t) ≤ 3t`, the exact startup, and the direct unbounded runtime proof. It
says itself that the source change saves no state. The change only completes the route
that makes the 223/182 sharing possible.

## Are the 236-state constructions different, and do they combine?

The intake canonicalized and grouped **every** table in Sources 112–114, including
research and rejected ones.

- **Exactly one sound 236-state machine.** All three packages accept the identical table
  `d4302309…`, in seven copies: Source 112 constructed it, Source 114 re-derived it, and
  Source 113 audited it.
- **Four other 236-state tables**, all in Source 112's `discovery/negative236/`, are the
  only *different* 236 constructions. Each rewrites the source to an equivalent one (the
  control graph equals the 237's) that still has 224 or 225 distinct subtrees, so no node
  is saved. Each then merges one decoder state: 190 (two tables), 244 or 238. Source 103's
  finite screen rejects all four, failing 1,125, 1,243, 240 and 1,705 of the 8,386
  instruction cases respectively. That agrees with Source 112's counterexamples.

**Combination.** The only sound state-saving idea in the three packages is Source 112's
rotation-enabled fold, and the 236 table already uses it. The other material is no
saving:
- Source 113's logical-basis variants cost 2–3 more source nodes;
- E667 has no state count;
- the affine invariants can only strengthen proofs, since fold discovery already runs on
  reachable behaviour.

The four rejected merges cannot be combined until repaired. Their failures match the
tag-breaking pattern of the intake's own rotation `R_163_225`
([intake 175](intake-175.md#the-intakes-search-below-236)), whose obvious repair
un-shares a state and cancels the saving. The intake's iteration of Source 112's method
on the 236 itself found no further sound fold.

## Consequence

Three independent deliveries (Sources 112, 113 and 114) and the intake's own replay now
agree on the 236-state machine. None of the batch-176 material changes the result of
intake 175: no machine below 236 has been found.

Non-claims from both packages: no Lean/Rocq or PA endpoint for 236, and no minimality.
