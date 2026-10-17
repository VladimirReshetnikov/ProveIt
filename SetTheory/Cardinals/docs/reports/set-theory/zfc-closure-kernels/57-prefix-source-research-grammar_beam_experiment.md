# Whole-cost beam search on the complete revised word

The selected candidate has **269 working states**: 206 decision nodes and
63 framework states, including dispatcher depth 8. It does not improve the
retained 268-state control. The actual backend compiled this count; charging
an assumed constant 62 would incorrectly report a tie.

`grammar_beam_experiment.py` keeps source19's exact revised complete word,
including GEN, all eight original logical rows, equality, original rho6,
base-four constructors, both vacuity arms, gates and cleanup. It changes only
closed-word sharing and rebracketing, using the unchanged source08 helpers,
source19 layout functions and Andrew James Wade backend. The source pin is
`297ab8df7e5de329605c3875b4934643b371a5e3`; attribution and licenses remain
as recorded in `layout_grammar_experiment.md` and the imported snapshots.

Unlike the prior randomized Re-Pair runs, this search keeps up to 128 grammar
prefixes at each round, ordered by decision nodes plus 55 plus actual dispatcher
depth. It considers adjacent pairs with at least two nonoverlapping replacements,
with separate coarse and primitive tokenizations. The run scored 103,596
candidate DAGs in 116.9 seconds. Both lanes exhausted their retained frontiers
after 26 rounds, before the 45-round cap. The selected coarse candidate has
26 productions. These are bounded heuristic results, not optimality claims.

The pruning key contains residual token expansions and the sorted production
expansion inventory. It is deliberately coarse: different binary parse trees
can share that key, and their state costs need not agree. The first retained
representative is used. Thus neither the key nor the beam cap establishes an
exhaustive minimum, and no such inference is made from the negative result.
The original scratch comment called these grammars equivalent; that language
was corrected during review before publication. Exact expansion preserves the
program word, but does not equate the discarded parses' compiler costs.

The selected grammar expands to the exact word, all its tokens have closed
break/continue interfaces, and its register/control leaf signature is unchanged.
The compiled table has 537 named rows, with the sole missing `1.inc/read1` row
normalized under the established undefined-row-halting convention to give
538 total binary rows. Every compiled decision edge was re-extracted.

The independent source08 path engine checks 4,533 operation pairs against a
217-node reference: 2,601 increments, 1,931 decrement tests with both successors,
and one halt. Both programs unfold to 6,460 operation sites. All six deliberately
corrupted certificates are rejected. This is executable finite RM evidence;
it proves neither the binary compiler nor a ZFC consistency endpoint.

The packaged fast replay regenerates the table, named table, labels, both DAGs
and the operation certificate identically to the original search. Generated
program artifacts stay outside the checkout because no baseline was improved.
The saved JSON includes the complete selected grammar, per-round search counts,
compiler measurements, certificate statistics, rejection controls and artifact
comparison results.

```sh
python Computability/BusyBeaver/Research/ZFC/grammar_beam_experiment.py \
  --output /tmp/zfc-grammar-beam-replay \
  --replay Computability/BusyBeaver/Research/ZFC/results/grammar-beam-results.json
```

Omit `--replay` to repeat the bounded search. The driver rejects output inside
the checkout and assertion-disabled Python. No Lean or Coq build is involved.
