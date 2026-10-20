# State sharing after one closed source reassociation

A bounded search after **25 source reassociations** tested **282,416 fold specifications** and found no survivor. It starts from both accepted 218-state constructions and changes their source layout before attempting a deletion. The rotated parents preserve source behavior and pass decoder-prefix binding, but have **not** received primitive-runtime or blank-startup certification. No new machine is accepted here.

| Accepted starting layout | Retained rotations | Fold specifications |
| --- | ---: | ---: |
| [Primary K218](../../candidate-k218/README.md) | 12 | 136,592 |
| [Contextual K218](../../candidate-k218/alternatives/contextual/README.md) | 13 | 145,824 |
| Total | 25 | 282,416 |

The family rotates `((A,B),C)` to `(A,(B,C))`, or conversely, when A, B and C are closed and halt-free. The two physical decoder states must each represent one source subtree, have pure right-moving rows, and the child state must have exactly one incoming transition from the parent. Every occurrence of the parent subtree is replaced simultaneously. Four transition rows implement the reassociation.

The [primary census](results/primary/census.json) and [contextual census](results/contextual/census.json) retain only layouts whose complete primitive words and both independent ordinal control graphs agree with their seed, whose first 37 initialization addresses are unchanged, and whose longest zero run is at most six. Every reached internal decoder state is checked against its intended transformed subtree relation. All retained layouts still have 205 distinct source subtrees and 218 working states. The original table and source of every retained layout are stored beside its census. Prefix binding does not check primitive leaf execution; preserving initial addresses alone does not establish blank initialization.

For each layout the fold family includes every ordered keeper/deleted pair involving either rotated state, with inherited actions and, when exactly one mapped action agrees, every possible action on the other branch. It also includes every other pair with exactly one common mapped action when the other action enters either rotated state as a helper, over both writes and both directions. Specifications repeated within a layout are counted once. The family has 86,388 inherited-action, 92,220 affected-pair and 103,808 changed-helper specifications. It does not cover arbitrary action pairs, every helper route or two successive source rotations.

The previous reviewed filter recomputes the all-initial-tape window invariant for each rotated parent, at radius 7 and positive block fuel 97. Every specification fails this bounded filter, so the separate independent fold checker is never invoked. The complete [result](results/search1/result.json) records 73.188 seconds, below the 180-second internal and 190-second external limits. The [compressed first-failure stream](results/search1/rejects.jsonl.gz) records every specification. A failed local join is an incomplete proof-search failure, not a semantic counterexample or a state lower bound.

The [independent review](peer-review.json) covers the drivers, source comparisons, literal table changes and recorded search accounting without repeating the search. `root` authored the two drivers; the source/decoder utilities are inherited K221 code. `drop_contract` authored the previously reviewed fast filter; the independent checker is the Source139 submission. The [publication map](publication.json) preserves actual scripts, outputs and layout bytes. A first contextual input-path failure and the narrow correction are recorded in [history](history/preparation-note.md).

Portable reproduction uses fresh paths from the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k218-continuation-search/rotation-folds/census.py --output /tmp/k218-rotations-new
timeout 190s python3 -B Computability/BusyBeaver/Research/ZFC/k218-continuation-search/rotation-folds/search.py --inputs /tmp/k218-rotations-new --out /tmp/k218-rotation-search-new
```

The portable drivers change paths and entry-point arguments only; they are source-reviewed without a second search. Original executed versions and the exact portability differences are retained under `history/`. No submitted wrapper, ancestor suite, checksum manifest or proof assistant is invoked. A future fold survivor would still require its independent relative proof and the rotated parent's complete runtime and blank-startup obligations before a 217-state construction could be claimed.

A [second-rotation follow-up](second-rotation/README.md) checked 1,387 additional
closed rotation specifications across these 25 parents. None creates two
states with literally identical pairs of transition rows. This small census
does not include general state-fold synthesis after two rotations.
