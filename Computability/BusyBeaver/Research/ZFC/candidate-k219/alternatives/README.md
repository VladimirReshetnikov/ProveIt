# Alternative 219-state layouts and checked row157 stacks

All six tables below have **219 working states**, a separate halt outcome, and a blank-tape start. No 218-state construction is claimed.

Source 141 supplies three alternatives to the accepted K219 construction. The zero-terminal source replaces eight guarded break leaves by zero decrements; retagged performs 81 source reassociations and corresponding continuation retags; composed combines the source changes using its own decoder rows. Exact delivered native labels normalize 301→102 and 302→120. See the [construction data](data/construction.json), [literal comparison](data/comparison.json), and [placement provenance](../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake187-placement.json).

| Original alternative | Canonical table | Complete source | Generic cases | Blank startup steps | Row157 stack |
|---|---|---|---:|---:|---|
| Zero-terminal | [219-state table](machine/zero_terminal/k219.tm) | [sites](machine/zero_terminal/sites.json) |6,175|313,845|[219-state table](machine/zero_terminal-row157/k219.tm)|
| Retagged | [219-state table](machine/retagged/k219.tm) | [sites](machine/retagged/sites.json) |6,167|312,707|[219-state table](machine/retagged-row157/k219.tm)|
| Composed | [219-state table](machine/composed/k219.tm) | [sites](machine/composed/sites.json) |6,175|314,043|[219-state table](machine/composed-row157/k219.tm)|

Fresh checks of all three originals passed: exact reconstruction, whole-source control-flow comparisons and zero-terminal guard checks, complete whole-tape startup, all generic unbounded primitive interfaces, independent runtime audit, and negative controls. The source checks validate the concrete hypotheses of Source 141’s separate ordinary all-natural source-equivalence proof; that mathematical proof is not inferred from finite tests. The [actual execution record](data/fresh-alternatives-result.json) and [selected certificates](data/fresh) retain this evidence; complete case lists are losslessly gzipped. The inherited logical calibration was not freshly replayed, and this is ordinary executable certification, not a new Lean/PA endpoint. Full reproduction code/logs are retained with the [intake evidence](../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake187-fresh-alternatives).

For each original, we additionally changed native row157/1 from 1L148 to 1L187. Separate [zero-terminal](machine/zero_terminal-row157/joint.json), [retagged](machine/retagged-row157/joint.json), and [composed](machine/composed-row157/joint.json) checks prove positive joint blocks with identical complete tapes for every source invariant context, from every binary initial tape. Each freshly recomputed radius 7 domain has 1,664 nontrivial contexts; maximum old/new blocks are 2/3. Every initial-halt negative control was rejected. Consequently these stacks inherit blank halting equivalence from their originals. Their finite startup times were not separately simulated; the exact canonical bijections are recorded alongside the tables.

The composed table is **not** the literal union of zero-terminal and retagged: row139/0 is 0L139 instead of 0R99. The row157 patch conflicts with none of the three constructions.

## The failed218 supplement and remaining search boundary

The [review](review.md) distinguishes Source 143's all-natural source alternatives, focused raw 220 pilots, specific counterexamples and unresolved searches. Our [own literal replay](data/failure-transfer.json) confirms that all four known wrong first-clean endpoints and all three infinite-continuation certificates for the fixed cooperative return-state deletion persist on every one of these six layouts: 42 checks and 182,964 transitions. This refutes those specific generic interfaces. It does not assert their failure on a blank run, repeat the full 872-action screen, or settle its 35 unknown actions.

A [separate shifted-head search](../../k219-shifted-fold/README.md) completed 1,031,840 inherited-action candidates on these six layouts with no survivor. Bounded diagram rejection is not semantic inequivalence or a state-count lower bound.

## Reproduce the added checks

From this directory, with assertions enabled and fresh outputs:

```sh
python3 -B code/replay_stacks.py --output /tmp/k219-row157-fresh
python3 -B code/compare_failures.py --output /tmp/k219-failure-transfer-fresh.json
```

Each row157 check has a 120-second timeout. The second command replays only the 42 explicit failure transfers. The executed original scripts and path-only successor diff are preserved in [history](history). Source 141/143 authors supplied the constructions and failed-return evidence; drop_contract authored the added comparisons, stacks and failure-transfer reader. Root owns the shifted checker; opening_encoder performed the fresh original-alternative verification. See [provenance](provenance.json).
