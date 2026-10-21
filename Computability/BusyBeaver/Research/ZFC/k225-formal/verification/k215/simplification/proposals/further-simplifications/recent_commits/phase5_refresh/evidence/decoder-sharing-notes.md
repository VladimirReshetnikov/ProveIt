# Context-aware decoder sharing: bounded investigation

This is a source read and a 1.16-second finite census, not a new checker, kernel result, or speedup measurement. Canonical sources and all proof caches were left untouched. The exact source/table pins and own script are in `result.json` and `census.py`.

## Current proof boundary

`generate_sites215_lean.py` partitions the complete source tree into 105 blocks and nine files. `SiteCoverage.allSites` checks the full path of every leaf occurrence; `allSites_sound` and `KSim.covered_of_allSites` then establish coverage of every actual consumed path. These obligations must remain. There are 4,751 leaf occurrences, 1,425 decrement occurrences, hence 6,176 separate branch cases. The 202 shared syntactic nodes comprise 179 internal node kinds and 23 primitive leaf kinds; they are not a substitute for occurrence coverage.

`KRuntimeCore.BoxLemmas` already shares the arbitrary-register primitive reasoning. Its `exec_sound` gives whole-configuration reachability for every symbolic gap and register file satisfying the branch assumption. A memoized segment must preserve that scope and track whether a positive number of concrete steps has occurred: an abstract step may merely change representation or invoke a previously proved macro.

## Conservative sound sharing key

For direct memoization of the existing executor, use the immutable machine table, branch assumption, **entire symbolic input configuration** (state, head-side flag, complete left/right segment lists), and the requested segment endpoint contract. A cache of the bounded function `exec` also needs its target predicate, remaining fuel and `moved` flag. Semantic reachability lemmas can avoid target/fuel in the segment key if they return an explicitly checked endpoint and a positivity flag, and each caller separately checks its final target and composes the segment proofs. Merely using normalized configurations needs a proved concretization-equality transport; normalization alone is not a theorem about execution's chosen representation.

This exact key is safe but may share little: the full input contains the occurrence pointer. A practical first abstraction is a **whole-tape dispatcher frame lemma**.

A local dispatcher class consists of:

* fixed machine table and entry state;
* a finite relative-cell assignment covering every cell read by the proposed trace (including predecessor marker bits);
* a checked concrete trace, positive length, and exact exit state/head displacement;
* its frame conclusion: every tape cell is restored.

For any whole tape satisfying the assignment, induction on the fixed trace proves the same exit and unchanged entire tape. The untrusted producer may propose classes; a generic small checker and its ordinary induction prove them. No assumptions about unvisited exterior cells, register contents or source program are needed. For the present census, all exits advance exactly one pointer cell. The current pointer prefix and initial marker supply the local pattern hypotheses at each occurrence. Composition then preserves the unread suffix, gap and register box. Branch assumptions are irrelevant during this dispatcher portion, so its theorem can serve both decrement branches.

After dispatcher sharing, keep the existing exact primitive-entry and return obligations. A later return-frame abstraction must additionally preserve the CB/CC ancestor boundaries, branch polarity, effect on the box, overflow/marker behavior and complete expected exit path. No return-sharing count was measured here.

## Finite census and counterexamples

The own script independently parses the accepted source and native table. For every internal-to-internal edge, it runs at most 100 literal steps using only the known pointer prefix plus its start marker. An outside read is rejected. It requires positive length, unchanged complete known tape and one-cell advance. There are 4,749 such occurrence edges, using 165 physical states.

Grouping by entry state, every initially required relative bit, exit state and exact relative trace gives **281 classes**. Their traces total **353 concrete steps once per class**, versus **5,721 steps across the 4,749 local edges**. There are 252 classes requiring no predecessor bit, 25 requiring one, and four requiring two. These are local frame-edge counts, **not** total `KSim.checkEdge` work or Lean kernel workload; no matching runtime, memory or proof-size reduction follows from them.

A key containing only state and current bit fails on twelve state/bit pairs. For example, entry state69/read0 has:

* prefix `111110`: preceding bit1, exit105;
* prefix `1101001001110000`: preceding bit0, exit104.

Both restore the tape and advance one cell. The preceding bit is therefore part of the contract, not dispensable metadata. The result contains eleven more collisions, including state76 whose read0 traces require two predecessor bits.

Syntactic subtree equality also does not fix full return ports. The repeated subtree `(CI6, CC3)` occurs at prefix `01011`, with CC3 path `010111` returning to `010`; the same subtree at `11010010010000110011` has its CC3 leaf return to `110100100100001100`. Both exits leave the local subtree. A parameterized common theorem may transport them, but erasing the occurrence ancestry cannot.

## Bounded next experiment

Prove one generic local-frame trace checker, then certify these 281 classes. Add a dispatcher-to-entry composition theorem while preserving the existing complete `allSites` coverage and per-occurrence tail checks. Benchmark a single existing block before migrating all blocks. This is narrower than rewriting the register-box proof or introducing a new semantic relation. The investigation stops here; no candidate compiler invocation was performed.
