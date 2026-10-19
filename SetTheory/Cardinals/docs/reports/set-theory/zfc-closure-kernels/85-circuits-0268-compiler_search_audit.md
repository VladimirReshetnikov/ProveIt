# Independent audit of emitter provenance and plateau scope

This audit concerns the supplied search implementation and its finite
record. It does not provide a lower bound on Turing-machine states.

## Emitter provenance and positive-certificate boundary

The Context246 emitter is an adaptation of the attributed historical
source27 `cost_search.py` emitter. Its decoder-entry data have exactly
the same parsed JSON value as the preserved source27 data; only file
formatting differs. The historical source-code SHA-256 is
`bdc09619a4180b94eef1feaec03ef2a5f95cee9d4f3f13a899cd686d8e2a87b1`.
The historical metadata file hash is
`ef88e495ed21f050568234ab4d462c521f43bf3cceabf189839b1cd964e82751`;
the reformatted metadata hash is
`8c86224d2cfd90d8b76f322e43d45c2201a8312186d51e18f496e22d25b653e0`.

The substantive adaptation uses the exact Context246 literal table,
changes the logical-to-physical register map to `(6,2,0,4,3,7,8,5,1)`,
and starts fresh state allocation at 256 because old label 255 is already
occupied by a retained runtime pulse state. The dispatcher remains old
state 96. The emitter reuses modal inherited entries for matching
subtree fingerprints and allocates fresh entries for changed subtrees.
It emits only the dispatcher/fresh rows into a copy of the inherited
table. The optional shortened-detector experiment changes an additional
specified detector row and removes old state 74; it is not part of the
two complete positive layouts.

The inherited entry metadata contain context-sensitive/opaque cuts.
Consequently fingerprint reuse is an experimental code-generation
heuristic, not a general semantic compiler theorem. A program's finite
source graph, every binary instruction segment, macro support, and blank
prefix must be certified for the actual emitted bytes. The five retained
runtime layouts receive those source and universal runtime checks;
only layouts 0 and 233 also receive complete blank initialization.

The positive delivery verifier independently reparses the source program,
reconstructs the selected rotations, compares the complete leaf graph,
reruns the macro induction checker and all 8,391 affine instruction
cases, checks every pruned row against emitted rows, and binds the exact
blank traces and canonical renumberings. Its conclusions therefore do
not depend on assuming the modal-entry heuristic correct in general.

## Precisely scoped plateau enumeration

The search begins at the interned original decoder and applies the
implemented directed global shared-subtree operations: the two permitted
closed reassociations and adjacent distinct-increment commutation.
A mutation acts on every occurrence of the chosen shared node, interns
identical subtrees, and removes unreachable nodes.

This directed operation need not have an inverse among the same global
operations. A rewrite may make a new subtree identical to an existing
subtree; interning merges them, after which the nominal inverse may
rewrite both occurrences. The result should therefore be described as
queue exhaustion under the specified **directed rewrites**, not as an
unqualified connected component of all equivalent layouts.

The shape gate requires maximum consecutive zero run at most 7 and
maximum decoder depth at most 39. The table cost is the following
particular charged metric. Let `g` be graph reachability from old start
95 using both read rows, with halt excluded. Then

```
charged_cost(T) = exact_bisimulation_classes(T)  if g <= 249
                  g                             if g > 249.
```

The admission gate is `charged_cost <= 247`. A machine with more than
249 graph-reachable states could have an actual exact quotient of size
247 or less and be rejected by this shortcut. Therefore this search is
not exhaustive for a gate defined by the actual minimized cost alone.
Graph reachability also overapproximates the blank execution and does
not establish a reachable-context invariant.

The recorded run exhausted its queue:

| Recorded quantity | Value |
| --- | ---: |
| Expanded admitted layouts | 364 |
| Proposals generated | 86,800 |
| Distinct rooted structural fingerprints encountered | 84,700 |
| Admitted cost246 layouts, including the initial layout | 56 |
| Admitted cost247 layouts | 308 |
| Remaining queue entries | 0 |
| Cost below246 found | None |

The histogram omits the initial layout, so its cost246 entry is 55.
The histogram counts plus the initial entry total 84,700. The run's
elapsed-time and expanded-node limits did not stop it: `completed` is
true because the queue is empty.

Marking a rooted structural fingerprint as visited before applying the
gates does not introduce path dependence: the shape, emitter support,
and charged cost are properties of the interned rooted layout, up to
fresh-state renumbering. Revisiting the same structural form through a
different accepted predecessor cannot change those gates. The recorded
deduplication is by the supplied SHA-256 fingerprints; no stronger
claim of an independently serialized collision-free enumeration is made.

These facts support the finite queue-exhaustion claim for this
fingerprint-deduplicated directed search with these gates. They do not
certify universal runtime behavior or blank initialization for every
expanded layout, and they imply no minimality result outside the stated
search family.
