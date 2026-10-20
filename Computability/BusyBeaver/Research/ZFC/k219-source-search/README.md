# K219 contextual source search

No smaller machine was found. The useful results are an open-sided
association rule, a bounded search across whole-program sharing choices,
and all-natural proofs for five submitted equality alternatives that avoid
right-child decrements. The exact219 Lean/PA endpoint is not established here.

The reference is the accepted [K219 source](../candidate-k219/sites219.json).
Its206 distinct subtrees include primitive nodes; it has4744 leaf occurrences,
maximum depth38 and maximum zero-run6. Decoder states are a separate count.
The submitted equality-hit library is retained as
[Source140 data](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/140-k219-res-enc-eq_clean_hits.json).

The successor [84 membership/equality stacks](hit11-and-stacking.md) also
found no extra DAG saving: best205, matching the membership-only parents.
That note proves hit11's all-natural contract and preserves all84 sources;
the membership-calculus calibration remains open.

## Results

| Family | Measured result | Scope |
| --- | --- | --- |
| Both global single rotations at every DAG node | 295 attempts;210 preserve the exact full CFG;87 have206 nodes and123 have207 | Exhaustive for this one-step family |
| Open-safe rotation beam | 182256 attempted moves over30 rounds; best206 | Incomplete30-wide beam |
| Rotation plus commuting affine blocks | 187446 attempted moves over30 rounds; best206 | Incomplete15-best/15-uphill beam |
| Total affine block recognition | 35 blocks,35 distinct transformers; four cost-neutral swaps | Limited recognizer, no general non-equivalence claim |
| Current seed invariant | 6161 guarded closure edges; dead4607/4719/4720; forced-zero4606/4718 | Sound all-natural Cartesian abstraction |
| Known cleanup removals, composed with K219 | DAG208,207,209 separately/combined | Exact retained CFG quotients; source-only |
| Known six-leaf constant-one test, composed with K219 | DAG208;4738 leaves | Same whole-program boundary contract; source-only |
| Five no-right-decrement equality hits | 970 finite cases pass; separate all-natural proof | No new binary runtime certificate |

An independent [source peer](source-proof-peer.json) read the five all-natural
equality contracts, including the exact hit2 AST, without a compiler or runtime
claim. The [proof](proof.md) explains the all-natural arguments and the assumptions
that failed. In particular, `((A,B),C)` can be reassociated when A has no
escaping break and C has no escaping continue, even if B is open. Both side
conditions are necessary for this rule; explicit counterexamples are given.
Fewer leaves increased the DAG cost in the tested no-op specializations.
Conservative liveness also rejects simply leaving scratch counters dirty on
nonhalting equality exits.

The five alternate macros are **submitted Source140 synthesis hits**, not
newly discovered macro trees. Their all-natural clean contracts and their
exact composition with K219 are proved here. All five yield207 DAG nodes
and maximum zero-run6. Hit2 retains4744 leaves; hits0/1/3/12 have4748.
The [exact hit2 source](candidates/hit02.sites.json) is the most compact
no-right-decrement candidate in this library.

Removing right-child decrements does not by itself remove native state302:
that helper also handles a break return. The separate decoder lane reported
that hit2 initially lacked a generic right-child CI6 entry; with an explicitly
unverified symmetric entry, its raw allocations had220/240 states and retained
302. Those measurements are outside this source packet and are not runtime
proofs. No218-state or improved machine claim follows.

## Reproduction

From the repository root, using Python3 with assertions enabled:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k219-source-search/audit.py \
  --output /tmp/k219-new-audit.json
python3 -B Computability/BusyBeaver/Research/ZFC/k219-source-search/search.py \
  --output /tmp/k219-new-rotations
python3 -B Computability/BusyBeaver/Research/ZFC/k219-source-search/search.py \
  --affine --output /tmp/k219-new-affine
```

Use fresh output paths. The scripts import only this packet's own model and
DAG implementation and Python's standard library. They execute no delivered
compiler, Turing runtime checker, Coq or Lean. The beam is limited to30 rounds,
30 selected roots, at most3million interned nodes after a round, and120 seconds
checked after each round. Time/space bounds can cause an incomplete run;
`completed_rounds` records the actual scope. The two preserved completed runs
finish all30 rounds. They are deterministic in source choices for seed219206.

[Current audit](results/audit.json) records literal regeneration of all five
candidate sources, both CFG resolvers, finite diagnostics through selected
inputs10000, and the exact abstract closure. Search results are
[rotations](results/rotations.json) and [affine](results/affine.json), with
adjacent raw stdout. Earlier exploratory source/result files are retained in
[history](history/); the initial root-return modeling assertion and the
aborted memory-heavy frontier experiment are disclosed in
[history.json](history.json). No outcome is inferred from the aborted search.

## Prior work and attribution

Source140 already supplied the16 equality hits and finite tests; only hit10
was the accepted219 macro. Source137 already supplied reachable no-op and
constant-one specializations, and Source140's experiments already searched
closed-frontier reassociations. This continuation does not claim those ideas
as new. It adds the exact open-sided rule/search, affine commutation search,
current219 composition costs and explicit all-natural proofs for the five
left-decrement alternatives. See the accepted candidate's
[attribution](../candidate-k219/ATTRIBUTION.md), [licenses](../candidate-k219/licenses/)
and [intake186 reconciliation](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-186.md).
