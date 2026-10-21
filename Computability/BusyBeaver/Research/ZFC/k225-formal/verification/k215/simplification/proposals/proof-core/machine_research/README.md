# Targeted state-elimination research and a formal logical obstruction

This packet supplies **no 214-state consistency machine**. It contains a new, explicitly bounded edge-specific state-elimination experiment on seven existing 215-state machines, a successfully compiled standalone Lean countermodel for one logical-only simplification route, and an independent review of the balanced normalized source checker.

## Exact source snapshot

All seven machine tables were fetched through GitHub at ProveIt commit `aa66d0a33f1f8237a348899eb8095b045a502832`. `input-sources.json` maps `input0.tm` through `input6.tm` to paths relative to `Computability/BusyBeaver/Research/ZFC/`; the two result files pin every table by SHA-256. Their original start labels are preserved (in particular, GC-ZC215 starts at 74). All have 215 working labels, two rows per working label, and native halt 254. The inputs are existing constructions, not new machines from this packet.

## What the new finite search allows

For a proposed removed state q other than the start, every incoming row `(p,b)` with `p != q` can independently choose its own new write bit, direction, and surviving target (including halt 254). This is more general than redirecting every occurrence of q to a single survivor. Different incoming histories may use different helper states.

The abstract invariant is the least reachable set of `(state, local binary window)` configurations, starting with **every** initial window at the machine's specified start. Every head shift introduces both possibilities for the unknown new exterior bit. Closure therefore covers every tape from that start, including blank, but is not an assertion that every abstract configuration is concretely reachable.

For every permitted local window of an incoming row, the candidate replacement must join a positive old execution with identical control, head position, and local tape. Both executions have the stated step cap and may not read beyond the stated window. Untouched exterior cells therefore agree. The new block may not enter q or execute another incoming-to-q row in its strict interior. Joins are checked before this last restriction, so endpoints can be subsequent patch sites. This ensures that independently certified incoming replacements compose when applied simultaneously. Positive block lengths give a stuttering argument preserving halting and nonhalting. This sufficient argument is ordinary mathematics; the search is not kernel-verified.

The current search tries each nonstart q, considers its incoming rows in descending invariant-context count (native label breaks ties), and stops that target's search at its first incoming row with no qualifying replacement. It consequently does **not** enumerate every complete patch assignment, and `tested_replacement_rows` counts branch options actually tried. The provider states' own rows stay unchanged. Failure can reflect the finite abstraction/window/step restrictions and is not a semantic counterexample or a state lower bound.

## Results

| Window radius / join cap | Tables | Removable table/label pairs | Replacement rows tested | Incoming edges admitting a replacement | Complete state eliminations |
|---|---:|---:|---:|---:|---:|
| 5 / 64 | 7 | 1,498 | 1,291,720 | 4 | 0 |
| 7 / 192 | 7 | 1,498 | 1,299,460 | 13 | 0 |

These two runs examine overlapping families; do not add their target counts and call them distinct candidates. The radius-7 invariants contain between 970,351 and 987,611 nonhalting local configurations per table. The omitted halt configurations explain why these counts can differ from earlier invariant implementations that retain terminal states.

`positive-control.tm` contains a known three-step detour. The search finds two valid eliminations, including deletion of state 1. This is an algorithm sanity check, not verification of the K215 semantic theorem.

The radius-7 result lists every successful incoming-edge replacement found before the first obstruction. For example, on FT215 it admits:

- `26/1: 1 R 38 -> 1 L 114` (13 possible replacement actions in the search family);
- `26/0: 0 R 134 -> 0 R 194` (one possible replacement action).

These are relative to the proved-by-construction abstract reachability invariant, not unconditional all-tape equivalences from arbitrary control states. Other incoming edges still obstruct deleting 38 or 134. These partial results suggest a concrete next experiment: combine an engine-return rewrite with a **new decoder allocation**, or permit one provider-state row to change while eliminating the target. Another route is a simulation allowing state-dependent head offsets. Neither is covered by the present negative results. Do not promote these partial substitutions to new accepted binary candidates without the complete state/table and simulation checks.

The existing context-return alternative already includes `13/1:1L31 ->1L81`; rediscovering that edge is a control rather than a novelty claim.

## The logical result and its boundary

`HiddenCoordinate.lean` proves a precise nonderivability statement in a logical fragment stronger than the logical part of the late-matrix inflation experiment. Membership is interpreted at valuation e as `e(0)=false and e(a) != e(b)` over Bool. Every retained logical schema, all equality-vacuity schemas, and membership vacuity for `c>a+b` are valid. The missing instance `R(1,2) -> forall_0 R(1,2)` is false at `e0=e1=false,e2=true`.

The proof explicitly excludes the set-theoretic seed bundles. It does **not** prove that the complete large-matrix calculus is too weak, and does not rule out a different consistency translation. The one-page include-only `hidden-coordinate-note.tex` gives the argument and practical interpretation. `HiddenCoordinate.check.txt` is the successful Lean 4.32.0 output, with no `sorryAx` dependency.

## Truth and physical initialization

Removing a separate truth constructor from an abstract implication proof does not immediately save a physical state. K215 has no distinct instruction that emits a truth axiom. Its code zero occurs as reset data, initial top/cache values, and Cantor-stack termination. In the actual coding, `rho8(0,0,0,0)=0` already derives it. The binary bootstrap builds the interpreter frame and enumeration seed, using states subsequently reused by the runtime. If the implication coding is changed to remove its zero alias, these concrete zero values still need a sound logical interpretation or a separate protected-data bootstrap. The new abstract theorem alone supplies no table-level elimination.

## Reproduction

With Python 3 and a C++17 compiler:

```sh
python3 reproduce.py --work /tmp/k215-edge-replay
```

The work directory must not exist. To also recheck the standalone Lean proof:

```sh
python3 reproduce.py --work /tmp/k215-edge-lean-replay --lean /path/to/lean
```

Use Lean 4.32.0 with its standard `Std` libraries. The script rebuilds the search, checks its positive control, pins all input hashes, reruns both finite searches, and checks exact receipt equality. It uses no network, optimizer, or external repository checkout.

## Attribution

The seven machine inputs and their mathematical correctness arguments are inherited from Vladimir Reshetnikov's ProveIt repository and the individual alternative packets, whose notices and predecessor credits remain authoritative. `inherited-notices/` preserves the notices available with the frozen inputs. This packet contributes only the edge-specific bounded search implementation, its scoped results, the standalone logical countermodel, and the review. New files follow ProveIt's MIT No Attribution terms; inherited files retain their own terms.

## Follow-up: a certified FT215 shortcut frontier

`ft_frontier.py` independently proves simultaneous native row changes
`26/0: 0 R 134 -> 0 R 194` and `26/1: 1 R 38 -> 1 L 114`.
The actual resulting 215-state table is `ft-frontier/machine.native.tm`, SHA256
`c912529b89e0ef26970b03ea63917890563a8b202b2982639e89510901577570`.
The source remains the current FT215 `ft-source.sites.json`.

The proof computes an inductive abstraction of 971,847 state/window pairs,
starting with **every** 15-bit window at control state 0. Thus it covers arbitrary
initial tapes at the designated start, including the blank tape; it does not
extrapolate from a finite blank run. Each of the 4,736 row26 contexts has an exact
positive old/new local join, with no exterior reads and no other altered row
executed in the strict new-block interior. The 4,736-row finite certificate is
included. Joining preserves the whole outside tape because neither path touches
it. Positive progress and the inductive invariant permit repeated block matching
and establish the same halting behavior. This is ordinary executable mathematical
evidence, not a new proof-assistant theorem.

`ft_runtime_census.py` separately rederived **all 6152 arbitrary-natural primitive
cases on both exact tables**, including fresh list-block induction schemas. The
baseline uses 1,617,650 symbolic rules and the modified table 1,618,486. Both cover
all 430 transition rows. `ft_startup.py` matches the baseline blank checkpoint at
70,506 steps to the new table at 70,526 steps, with exact state/head/whole tape.

The shortcuts remove engine uses of 38/0 and 134/0, but add uses of 46/0,107/1,114/0,
114/1,126/0 and194/0. Engine obligations grow 144 ->148 rows (80 -> 82 states).
The row26/0 shortcut alone is the cleaner remaining direction: it replaces a
literal two-step path by another two-step path. The longer row26/1 detour has an
unfavorable engine cost. This packet does not assert a 214-state construction.

The bounded allocator then tried deleting 38 or 134, with the current source and
15 existing contextual aliases pinned. It protects the newly observed engine
rows, decoder helpers and initial bootstrap (210 protected rows in total).
Its no-deletion control reproduces the exact table without any row changes.
Both deletions fail: an independently constructed Hall witness gives 115 distinct
decoder roles with only 114 allowed physical slots, before considering the extra
child-target constraints. The JSON files contain the complete role/domain/slot
witnesses. The MILP solver also reports infeasibility (14,793 variables and 1,237
constraints per deletion). This is an obstruction to this exact model, not a
state-count lower bound or a claim about all contextual encodings.

The remaining source decoder entrances are 188/1 ->38, for prefix 11 (left child
CI6), and 312/1 ->134, for prefix 001 (left child CD3). Both right children are
nonterminal. A productive next attempt must change this role structure, admit an
additional contextual alias, or replace a protected engine/helper row with a
separately proved implementation. Merely relocating these fixed roles cannot
fit the recorded model.

Replay the local certificate, exact startup and allocations with NumPy/SciPy:

```sh
python -B reproduce_ft.py --work /absolute/path/to/empty-ft-replay
```

Add `--runtime` to rederive both complete arbitrary-natural runtime proofs; this
usually takes a few minutes. `ft-replay-receipt.json` records the packaged fast
replay. The saved baseline/new runtime receipts came from fresh complete runs,
not only a saved-receipt audit. Runtime helpers and source-tree utilities are
inherited, bundled under `vendor/`, with their notices preserved under
`inherited-notices/`. The FT allocator is a new adaptation of the inherited protected-allocation model; its original script is included for provenance. The independent local certificate code is new here.

The new four-shape rho8 completeness theorem from the companion proof work is a
valuable source-design alternative, but does not itself remove a physical row:
the current numeric guard shares arithmetic machinery, while four structural
constructors introduce nested implication terms and additional source branches.
Any state-saving claim needs a compiled emitter and a fresh decoder allocation.
