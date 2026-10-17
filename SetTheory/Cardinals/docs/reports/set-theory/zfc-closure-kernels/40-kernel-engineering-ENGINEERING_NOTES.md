# Public 253-state audit and bounded transition surgery

This directory examines the attributed public 253-state machine from
`mira-emmy/busy-beaver` commit `0d544f2a2e3c18f12278441a74b7879f31cbe856`,
submitted as [jeff87654/busy-beaver PR 20](https://github.com/jeff87654/busy-beaver/pull/20).
The 254-state predecessor is Mira-Cult's design. Jeff's development verifies
it; mira-emmy supplies the 253-state reduction and its table-specific proofs.
No new state record is claimed here.

## Reproduced exact results

`python3 audit.py` independently checks the pinned literal bytes, regenerates
the four-row reduction from the 254-state table, computes graph reachability
and exact state partition refinement, simulates every actual bootstrap step,
compares every tape cell with the specified target, and computes the 330-step
register-machine prefix from the pinned Coq program table. It also replays
the upstream Python affine model on all 6,460 instruction leaves (8,391 cases,
because decrement has two branches). The checker runs offline.

The blank run reaches compact state 33 (old label 96), head -17, after 312,975
steps. The PC is 000, head-to-header gap 40. Logical registers are
`[5,0,0,0,2,0,0,0,0]`, physical registers `[0,2,0,0,0,0,5,0,0]`. The 158 spare
blocks have value 1 at indices 2 and 8 and 0 elsewhere. The entire finite
support consists of 178 one cells. These data are in `audit.json`.

All 253 working states are graph reachable. Exact partition refinement gives
14, 60, 128, 195, 228, 235, 242, 247, 249, 251, 252, 253 working classes; the
next round is stable. Thus this literal table has no nontrivial state quotient
that preserves every exact transition's output symbol, direction, and target
class. This narrow fact does not restrict changes of the program, tape coding,
initialization, or simulations with differing numbers of steps.

The Python affine replay uses the upstream register-box oracles. It is not
an independent proof of those oracles, nor a Coq rebuild. `coqc` is unavailable
in this execution environment. In particular, none of these computations alone
proves an arithmetized consistency equivalence inside ZFC.

## New bounded search

Run `python3 reproduce_search.py --radius 20 --fuel 128` to reproduce the full
experiment. It takes roughly a minute in the reference environment and needs
a C++17 compiler (`g++`). It generates a large, disposable context catalog;
archive the scripts and compact summaries, not the catalog or compiler binary.

For each eligible deleted state, every incoming transition may change its
write bit, its move direction, and its target state. This extends searches
that only redirect the target. The selected 221 states exclude the start,
dispatcher, deleted old label 8, and protected register-engine states, and
require incoming sources outside that protected set. Deleted-state self-loops
vanish and require no redirection. There are 412 watched
incoming edges. Exact symbolic instruction traces and the entire exact boot
provide a catalog of local partial tapes. Unknown register-file cells remain
unknown. At radius 20 the catalog has 1,176,597 patterns; at radius 10 it has
171,450 patterns.

For each incoming edge, the C++ search considers every write/move/target
combination with an existing target (including the terminal), except the
deleted state. It checks whether the changed edge and the original edge
converge to identical state, head, and local tape in at most 128 moves per side,
without the alternative visiting the deleted state or reading an unknown
cell. Every incoming edge of a state must pass. The search stops at the first
incoming edge that has no certificate. It tests 226,688 edge alternatives and
finds zero complete deletions. The smaller radius-10, fuel-32 experiment also
tests 226,688 alternatives and finds zero deletions. The final radius-20
context collection took 28.996 seconds; the C++ local search took 0.186 seconds.
Both timings exclude compilation. Timings depend on
the host. `search_timing.json` retains the measurements.

The C++ checker includes six focused controls (`./confluence_search --self-test`):
it accepts a route whose first move reverses direction and a route whose changed
first write is later restored; it rejects a permanent wrong tape, a route missing
the necessary temporary write, a visit to the deleted state, and an unknown-cell
read. These controls exercise the extra write/move freedom explicitly. They do
not make the bounded search a complete equivalence decision procedure.

This outcome states only that this finite certificate search produced no
deletion. Missing contexts, protected engine edges, changing several other
rows together, long excursions, different instruction boundaries, and a new
initializer all lie outside its claimed coverage. Failure to converge in the
bounded window is not a proof of semantic inequality. Every candidate would
still need a universal instruction check and a calibrated blank bootstrap.

## Files and upstream provenance

The `upstream/` files are verbatim source material fetched from the pinned
public PR commit. Their original notices and READMEs are retained. They are
not newly authored by this work. The audit/search scripts and this note are
new support material. The fetched Coq files are reference inputs, not a full
buildable proof closure. A full upstream proof build requires the pinned PR
checkout and the dependency closure listed in its `ZF/m253/check.py`.

Primary paths:

- `ZF/m253/machine/zfc_253.tm`: SHA-256
  `84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95`.
- `ZF/m254/machine/zfc_254.tm`: SHA-256
  `d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb`.
- `ZF/m254/coq/tm/Prog254.v`: SHA-256
  `1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746`.
- `ZF/m253/coq/e2e/E2E253.v`: the public external finite-refutation endpoints.
- `ZF/m253/coq/tm/Boot253.v` and `Prefix.v`: exact bootstrap and prefix transport.

The public proof endpoint is a finite classical refutation of a concrete
formal theory (`ZFc + AC`). For the user's internal ZFC target, the connection
between that formal proof predicate and the chosen arithmetized ZFC predicate,
including Foundation/Regularity, must also be supplied. The current upstream
PR explicitly refrains from claiming internalization.
