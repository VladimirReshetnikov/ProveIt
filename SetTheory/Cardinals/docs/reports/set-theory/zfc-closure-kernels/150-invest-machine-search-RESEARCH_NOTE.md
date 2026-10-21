# Independent machine-side investigation

This directory contains exploratory machine searches based on the published K218 native table and the distinct incoming contextual K218 table. **No 217-state construction has been certified by this investigation so far.** Failed bounded diagrams are not lower bounds or semantic counterexamples.

## Inputs

- Public K218 native table: SHA256 `2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f`.
- Incoming contextual K218 native table: SHA256 `3c64cf321c9ca11153901cdb19e7326b8bfbd0d3c8d94357ead127a9c9b491c1`.
- Incoming row157 alternate produced here: SHA256 `02ec4a475115217cd836f755e2806ba65a842a6377d13c7975a8ec81045819a5`.

The incoming and public constructions use the same conceptual marker fold on different source allocations. They differ in 73 table rows. Public-only physical states are96 and190; incoming-only states are79 and212. Their deleted-state labels therefore do not identify independent reductions that can simply be stacked.

## Completed results

| Family | Specifications / result | Record |
|---|---:|---|
| Incoming all-state inherited/one-common-action folds |642,320 rejected | `incoming_folds/result.json` |
| Incoming row157 all-state inherited/one-common-action folds |640,584 rejected | `incoming_row157_folds/result.json` |
| Public one-row changes |381,500 tested;463 pass local diagrams; none reduces graph-reachable states | `single_public/result.json` |
| Incoming one-row changes |381,500 tested;472 pass local diagrams; none reduces graph-reachable states | `single_incoming/result.json` |
| Public common-branch fold plus one additional individually admissible row rewrite |5,701,222 tested; no survivor | `extra_general_merge/result.json` |
| Public marker-complement folds with inherited/common-branch actions |462,067 tested; no survivor | `flipped_merge/result.json` |
| Public marker-complement folds, two preserved-bit/left-moving actions |4,562,304 complete assignments covered by46,530 partial tests; no survivor | `flipped_twoaction/result.json` |
| Public marker-complement folds, arbitrary two actions |72,996,864 complete assignments covered by304,424 partial tests; no survivor | `flipped_fullactions/result.json` |

The stronger extra-row experiment includes the earlier44-ordered-marker-pair experiment (604,589 alternatives) and should not be added to it as a count of disjoint candidates. Counts in different families may overlap.

A separate global source rotation beam stopped after258,421 attempted moves, at3,033,170 hash-consed nodes, retaining best cost205. Root's independent source agent owns the broader source-DAG investigation, so this beam was not extended.

### A concrete new 218-state alternate

The incoming table admits the same literal rewrite

```
157 1 1 L 148  ->  157 1 1 L 187.
```

The unchanged independently authored `check_joint_fold.py` proves its relative all-initial-tape halting equivalence. It recomputed1,001,257 inductive contexts, checked1,280 nontrivial contexts, and used maximum old/new blocks2/3. A corrupted initial halt was rejected. The full receipt is `incoming-row157-proof.json`; the table is `incoming-row157.native.tm`. This is a checked alternate at218 states and does not solve the217-state target.

The one-row and multirow exploratory filters have not all been independently replayed. Their positive local-diagram outcomes are discovery evidence, not separate published candidate certificates. Final search status and exact remaining counts are in each JSON result.

## A broader configuration relation: complemented entry marker

Ordinary state-sharing searches insist that old and new tapes coincide at every matched boundary. That is stronger than necessary. Let old state r be removed and represented by a surviving state q. Suppose every incoming row into r from other unchanged states moves in direction d. Define the configuration representation by

- preserving state, head and tape at every state other than r;
- replacing r by q, leaving the head unchanged, and complementing the bit at offset -d from the head when in r.

An incoming row `(write w, move d, next r)` then maps exactly to `(write 1-w, move d, next q)`. Its written cell becomes the temporary marker. The new q rows must subsequently consume or restore this change, and the representation may be used again at later visits to r. No extra working state is required to establish the marker. This relation can distinguish source roles whose original written entry markers are equal, which the earlier same-tape quotient family cannot do merely by redirecting entries.

The implementation in `flipped_merge.py` checks positive common-endpoint diagrams on a radius7 all-initial-tape window invariant. At an old endpoint in r, it complements the appropriate endpoint-relative marker before comparison. It rejects a join when that marker would lie outside the known window. It explicitly checks every state for a survivor. Its current negative results do not require trusting its acceptance logic, but an eventual positive result should receive a separately authored checker and negative controls.

### Relative halting theorem

More generally, for each old state p choose a new state phi(p), a fixed head displacement delta(p), and a finite set S(p) of tape offsets to complement. Define

`F(p,h,t) = (phi(p), h+delta(p), t XOR {h+s : s in S(p)})`.

Assume the initial configurations satisfy this relation. Assume an inductive old-machine configuration domain, and that at every related pair in that domain either:

1. both deterministic runs halt in positive finite time; or
2. both runs make positive finite blocks, without an interior halt, to another pair related by F.

Then the two machines halt on their respective initial configurations exactly together. Proof: repeatedly concatenate the matched blocks. Positivity ensures that infinitely many blocks produce an infinite execution on each side; every finite old halt is reached after finitely many positive old blocks and is matched by a finite new halt. Determinism makes the concatenated blocks the unique executions. Uniform block bounds are useful for a finite checker but are not needed for this implication once finiteness and positivity of each block have been proved.

This is a general simulation principle, not a claim of novelty in automata theory. Its specialization to temporarily complemented entry markers expands the exact candidate family beyond the repository's same-tape and shifted-head folds. No successful K217 table has yet been found in the tested specialization.


## Later continuation

See README.md and the `results/twoaction_*` receipts for the later demand-driven C++ both-row search, finite source-mask experiments, and exact counts. The C++ search permits paths to revisit the modified keeper state; it is not restricted to precomputed unchanged helper chains. Assignment counts use sound partial-assignment pruning within the declared bounded local-diagram test. No negative result is a state lower bound.
