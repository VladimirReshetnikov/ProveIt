# Additional machine-optimization experiments, 16 October 2026

**Result: no new smaller consistency machine was obtained.** The strongest exact-word compiler control remains **268 working states**, and the attributed public **253-state** machine remains the smaller verified baseline. These files record genuine unsuccessful attempts, with narrowly stated finite verification, to prevent them from being reported as positive reductions.

## Inputs and attribution

The inputs are the ProveIt checkout at `4747142d5d15213eb711bdadfa3cc7e769fcb7a7` and Jeff's upstream checkout at `297ab8df7e5de329605c3875b4934643b371a5e3`. The 253-state table is the attributed PR 20 artifact at `0d544f2a2e3c18f12278441a74b7879f31cbe856`, retained in ProveIt as:

`SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/04-machine-machines-zfc_253.tm`

Its SHA-256 is `84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95`.

The compiler source is the **source-19 revised conjunction layout** behind the existing 268-state control. It keeps all eight original logical/equality rows, original rho6, four-tag formula coding, all arithmetic, and the enumeration framework. The layout recipe is C2/G1/outer-order16/tree1, identity parameter permutations, and the original logical-row order. We preserve its exact macro word; the only prior logical transport involved is the already documented source-19 conjunction commutation/association. The literal source-19 table itself is not the source of any new state record here.

Mira-Cult designed the original 254 machine and underlying register program; Jeff supplied its Coq verification; mira-emmy supplied the attributed 253 reduction. The invoked backend is Andrew James Wade's MIT-0 TMBuilder. Weighted Re-Pair, macro-bound checking, the path-bisimulation generator, and the independent path engine are inherited ProveIt source-08/source-19 tools. Their upstream files are loaded unchanged from the supplied checkouts. The new code here does not relicense those dependencies.

## Searches performed

| Search | Precisely executed scope | Result |
|---|---|---|
| Overlap-safe grammar sweep | 2 tokenizations × 2,048 seeds × exponents 1,2,4,8 = **16,384 trials** of the revised full-logic word | Minimum **268 = 206 decisions + 62 framework** |
| C++ overlap-safe grammar sweep | **200,000 trials**, seed 20261016, exact coarse word, exponents 1,2,4,8 selected by the recorded schedule | Minimum **268**, first reached at trial 3,423 |
| Restricted grammar MILP | **317 non-atomic substring variables and 912 binary-split variables**; all repeated substrings, their suffixes, and the complete word's suffixes; 120-second solver limit | A **270-state** control; solver time limit, **no optimality certificate** |
| Per-incoming-edge redirection | Literal 253; radius 4 and separately radius 6; remove a state by choosing a different target for each incoming edge; up to 64 additional local steps after the incoming transition | No accepted deletion |
| Per-incoming transition rewrite | Literal 253; radius 6; each incoming transition may change write, direction, and target to another working state; **231,131 attempted rewrites**, 229 eligible removed states | No accepted deletion |

The radius-6 abstract reachability computation contains **335,369** head-centered configurations. It admits both values for every newly exposed outside cell and therefore overapproximates the blank run. Radius four contained 31,909 configurations. The terminal halt target was not considered as a replacement destination. Initial states and states with self-loop incoming edges were excluded from the distributed-elimination searches. Most removed-state candidates fail on their first incoming edge; 235 incoming-edge tests were visited. The count 231,131 refers to attempted local rewrites, not an exhaustive Cartesian search over assignments to every incoming edge. A failed conservative sufficient condition is not a state lower bound.

The C++ search charges **decision nodes + 55 + maximum consecutive-left depth**. It does not assume the framework always costs 62: the dispatcher depends on the selected parse. Every saved best-so-far C++ grammar was independently expanded in Python, compiled through Wade's actual backend, and had all emitted decision edges re-extracted. All nine recorded costs (287, 286, 280, 277, 276, 275, 270, 269, 268) agree with actual compilation. This is a check of saved artifacts, not an independent rerun of all 200,000 trial evaluations.

The MILP minimizes enabled grammar nonterminals in its restricted substring family. This objective is a synthesis heuristic for the final TM cost. Its incumbent objective was 102, lower bound 78, and reported gap approximately 0.2353. The resulting grammar compiled to 207 decision states and an eight-state dispatcher, so the actual cost was 270. Neither the grammar nor the machine is claimed optimal, even within a larger family.

## Exact finite checks

`validation.json` records passing independent checks. The independent RM path engine is pinned by SHA-256 `30fbd95b7a2a61004422558cfab4419de5239b67b88bc9ed19b7de8fcf585f18`.

For both the emitted 268 control and the MILP 270 control, the generator's certificate was checked against the **217-node revised reference**, using that separate engine. Each has **4,533 related operation pairs**: 2,601 increments, 1,931 decrement tests, and one halt. Both decrement successors are checked, every record is reachable, and every contracted control chain is finite. Six deliberately corrupted certificates were rejected for each control: wrong initial record, missing record, duplicate record, wrong instruction, wrong zero exit, and wrong positive exit.

These certificates give the usual operation-level bisimulation argument for equal register vectors between those programs. They do **not** verify the unbounded binary interpreter, blank initialization, frontend proof enumeration, or an internal PA/ZFC consistency equivalence for a new table.

A 32-window positive control for the new local-join primitive checks a state deletion that skips a tape-preserving two-step excursion. A corresponding wrong-write variant is rejected on all 32 windows. The negative searches themselves are executable experiments, not proof-assistant-certified enumeration results.

## Why the distributed edge criterion is sound when it succeeds

Fix a proposed removed state p. Every incoming transition has its own candidate replacement. For every possible predecessor window in a sound blank-run overapproximation, perform the original incoming transition and the replacement transition, then execute each side locally until an identical state, relative head position, and window contents are reached. Both initial transitions count as positive progress. No later transition into p may be executed during this local comparison, and no transition reading outside the known window is executed. The comparison therefore uses unchanged table entries after its first step. Every written cell lies within the known window, so equal final windows and head positions mean equal full tapes for every compatible exterior. Future modified incoming edges are handled by the same condition. Concatenating these positive local simulations gives equivalence of finite halting and prevents a spurious infinite zero-progress simulation. Our search found no literal-253 deletion satisfying this sufficient condition.

## Reproduction

Run from a directory containing this folder plus the pinned `proveit` and `upstream-busy-beaver` checkouts. Python needs SciPy only for the MILP experiment; the grammar and table searches otherwise use the standard library. A C++17 compiler is needed for the accelerated sweep.

```sh
python machine_experiments/grammar_search.py --repo proveit --upstream upstream-busy-beaver --output machine_experiments/search16k --seeds 2048

g++ -O3 -std=c++17 machine_experiments/fast_grammar.cpp -o /tmp/zfc-fast-grammar
/tmp/zfc-fast-grammar machine_experiments/fast-coarse.input machine_experiments/fast-coarse-records.jsonl 200000 20261016

OPENBLAS_NUM_THREADS=1 python machine_experiments/grammar_milp.py --repo proveit --upstream upstream-busy-beaver --output machine_experiments/milp_expanded --time-limit 120 --lane expanded --free-161

python machine_experiments/edge_elimination.py --repo proveit --table proveit/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/04-machine-machines-zfc_253.tm --output machine_experiments/edge-elimination-r6.json --radius 6

python machine_experiments/edge_rewrite.py --repo proveit --table proveit/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/04-machine-machines-zfc_253.tm --output machine_experiments/edge-rewrite-r6.json --radius 6

python machine_experiments/validate_experiments.py --repo proveit --upstream upstream-busy-beaver
```

A time-limited MILP rerun can return a different incumbent on another host. The delivered grammar and its complete finite certificate remain independently checkable without rerunning the solver. No proof depends on a solver optimality claim.

## Artifact identities

The newly rebracketed 268 control's complete numeric table is `search16k/candidate.tm`, SHA-256 `169d97ddf7a1a722b3686aa414bd24a7bcf49c433b5c7b9e50fc1f20f356bed7`. This is a different 268 table from the source-19 winner, with the same exact revised source word and no new consistency endpoint. `milp_expanded/candidate.tm` is the 270 control, SHA-256 `b4a69923872943bacbf257b96b8f77b354cc6234b4f2250ac1124d6438837a78`.

Each control includes its literal table, named table, labels, source/candidate DAGs, exact grammar, RM certificate, and result metadata. Raw search logs and aggregate results document the unsuccessful attempts. None of the files is a new 252-state solution.
