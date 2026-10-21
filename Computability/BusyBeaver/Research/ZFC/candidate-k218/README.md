# A 218-state binary Turing machine for Con(ZFC)

The current primary contender is the [217-state construction](../candidate-k217/README.md)
from `8a1796545e`. This former primary and its verified 218-state alternatives
remain published for comparison.

This machine has **218 working states and 436 transition rows, including initialization**. Its ordinary mathematical proof gives

```text
ZFC proves: not Halt(K218, blank) <-> Con(ZFC).
```

The complete table is [k218.tm](k218.tm). It uses two symbols, blank 0, a two-way infinite single tape, L/R moves, initial state 0 and initial head position 0. Working states are 0–217. Halt label 218 has no outgoing transitions and is not counted. Each noncomment row is `state read write direction next`. The canonical SHA-256 is `06d7a91c583739e17f8b33ce3e03d0aeaf9e1faa186c76d596418942fe2a8730`.

The [native table](k218.native.tm) retains predecessor labels, dispatcher 84 and halt 254. Its SHA-256 is `2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f`. The [bijection and complete startup tape](canonicalization.json), [source](sites218.json), and [decoder allocation](decoder_allocation.json) bind the two presentations. **There is no newly compiled Lean/Rocq theorem for these exact bytes or internal PA endpoint.** No unconditional nonhalting or minimality claim is made.

A distinct [verified contextual 218-state alternative](alternatives/contextual/README.md)
is now published from `3c7c3aa5a3`. It passes complete runtime and blank startup
checks, reaching the same initial frame 208 steps earlier. Its final saving
merges the same two logical source roles, so it supplies another layout
without a further state reduction. This remains the reference layout for the 218-state alternatives.

Further complete 218-state alternatives from `7071e5041e` are now published:
[dominated rho8](alternatives/dominated/README.md), with 203 source subtrees;
[omitted MP zero push](alternatives/omit-zero/README.md); and
[DMN command tags](alternatives/dmn/README.md). Each has separately checked
full runtime and blank startup, with ordinary source/calculus calibration.
None reduces the working-state count below 218. The later [217-state construction](../candidate-k217/README.md)
at `8a1796545e` passed review and is now primary.

## Why one state disappears

A smaller source graph retains all 4,744 primitive instructions and their complete ordinal control graph while reducing distinct subtrees from 206 to 205. Its first physical allocation still uses 219 states. Five reassociations of a closed 52-instruction block then expose an existing decoder continuation without changing the source graph's size or behavior.

The resulting states 85 and 212 have a common zero branch. Their unique incoming transitions write different bits immediately behind the head: 0 before entering 85, and 1 before entering 212. The new table redirects both entries to 85 and uses existing states to reread that marker. On a scanned one, it reaches the respective old continuations in three or five steps, preserving the complete tape. State 212 can therefore be deleted. Relative to the accepted K219 table, 32 retained rows change and no state is added.

The [proof summary](proof.md) separates the all-tape final merge from source equivalence, unbounded primitive simulation, complete blank initialization and inherited finite-refutation calibration. The submitted source allocation and context-dependent reuse are the construction's contributions; the earlier uncalibrated K/S experiment is not a premise.

## Fresh verification

Six selected direct checks passed during intake:

| Check | Result |
| --- | --- |
| Source and literal construction | Delivered source/table reproduced; 205 distinct subtrees; 218 states |
| Independent source and state-fold premises | All 4,744 control vertices, five closed rotations and four two-cell cases |
| Native sparse and canonical dense startup | Exact complete frame after 312,909 transitions |
| Separate sparse startup audit | Complete support and first root-source frame |
| Full symbolic primitive runtime | 6,167 guarded cases; 1,515,158 rules; all 436 rows |
| Independent runtime audit | Complete ordered coverage, positive affine durations and four block schemas |

The runtime certificates quantify independent arbitrary natural register values, gaps and nonempty finite spare lists. Their minimum duration constant is 12. The finite symbolic construction bound does not bound those values. Startup reaches native dispatcher 84 (canonical 23), head −5, logical registers `[3,0,0,0,3,0,0,0,0]`, extra gap 80 and 130 value-one spares. The tape has exactly 277 one-cells and all other cells are zero. An earlier clean-looking dispatch at step 92,808 has a nonzero source address and is not the required endpoint.

Fresh [execution evidence](evidence/actual.json) and [selected certificates](evidence/) are retained. Full logs and regenerated case receipts are in the [intake evidence](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake188-fresh-k218/). The intake did not replay ancestor wrappers, manifest suites or a proof assistant. The unchanged K219 finite-refutation calibration is inherited through the proved source/runtime/startup bridges.

## A checked alternate layout and the next reduction

The existing rewrite `157/1: 1 L 148 -> 1 L 187` also works on K218. The [alternate native table](variant-row157/k218-row157.native.tm) and [canonical table](variant-row157/k218-row157.tm) still have 218 states. The unchanged independent checker freshly verifies 1,009,191 inductive window contexts, including 1,408 nontrivial contexts; positive old/new blocks are bounded by 2/3 transitions and a corrupted initial halt is rejected. See its [result](variant-row157/result.json). This is an all-initial-tape halting-equivalence proof, not a new literal startup-time measurement.

The earlier attempt to delete state 301 would produce 217 states after three additional row changes. It still has exactly the same 85-step failed blank prefix and then writes ones forever while moving right in state 35. The [literal transfer record](research/comparison.json) preserves that obstruction; this table is not a consistency candidate. The later [all-start audit](../k218-continuation-search/all-starts/README.md) proves that every one of its 217 possible working initial states reaches a blank ray, so changing only the start state cannot repair it.

The previous zero-terminal, retagged and composed source transformations can still be expressed on the new source and each retains 205 distinct subtrees. Their physical patches are disjoint from the K218 changes, but full machine correctness is a separate obligation. The rho6 parameter rewrite also leaves 205 subtrees. These [source-only comparisons](research/stack-syntax.json) identify possible alternate layouts; they do not establish a 217-state construction.

## Provenance and reproduction

Source 144, `K218_Construction_2026-10-20.zip`, arrived in commit `c4568161bf`. Its [intake note](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-188.md) and [recovery/replay guide](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-188-reproduction.md) preserve the complete submitted layout, main manuscript, exact technical payload and parent archive. The delivered main article and its inputs remain in that recoverable archive; this directory contains an independently written summary.

The [provenance record](provenance.json) pins copied bytes, the submitted [attribution](ATTRIBUTION.md) and [license](LICENSE). The exact K219 predecessor is preserved by intake and its [published construction](../candidate-k219/README.md). Source 144 contributed the source allocation, reassociation and marker merge. `drop_contract` independently reviewed the source and physical proof, prepared this summary, and checked the row157 composition; `review_upstream_reflection` independently reviewed the mathematical construction; `opening_encoder` executed the six fresh checks. The [review records](reviews/) distinguish their scopes.
