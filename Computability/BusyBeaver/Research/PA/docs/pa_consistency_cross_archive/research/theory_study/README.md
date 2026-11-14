# Theory and source composition study

This packet contains a new, executable **197-state** composition of direct negation with the diagonal-vacuity PA emitter. It also preserves a rejected attempt to remove the two freshness comparisons by padding a property code. Neither item is a construction below 196 states.

## Replay

Python 3 and the standard library suffice. No network access, search, Lean installation, or external checkout is required.

```sh
python3 -B verify.py
python3 -B replay_padded_failure.py
```

Run these commands in this directory. The first must print `"status": "PASS"`; the second must print `"status": "EXPECTED_REJECTION"`. The expected results are saved in `verification.json` and `padded_gate/rejection.json`.

## Successful composition

`direct_negation_diagonal197/machine.tm` is the complete two-symbol table, with working states 0 through 196, blank-start state 0, and halt label 197. Each row is `state read write direction next`. `machine.native.tm` is the same table with inherited labels; `labels.json` maps dense labels to native labels. The native start is 74 and halt label is 254. There are 394 transition rows.

The grammar, frozen five-fold allocation, serialized source, and receipts are included. `construction.py` reconstructs the table. `verify.py` pins the inherited files, checks the exact table and source binding, checks the emitted constructor terms, replays all 4,503 symbolic primitive contracts, and verifies the whole finite support of the blank startup tape after 58,154 transitions. The emitter has 3,468 primitive sites, 232 fewer than the diagonal 196-state parent, while the allocation uses one extra state. This illustrates why source size alone is not the machine-state objective.

The symbolic runtime inherits arithmetic-engine interfaces from the cited upstream package. Its success is an executable reconstruction check. This packet supplies no new Lean/Rocq kernel proof and no new internal PA consistency biconditional. The end-to-end mathematical scope remains that of the parent emitter and its proof bridge. `theory_results.tex` states the new arithmetic identity and the limits of the result.

In particular, the new negation macro requires `r6 = r7 = 0` on entry and preserves those zero values on exit. The free-constructor checker does not track these scratch registers. The primitive runtime checker verifies implementation of each primitive for arbitrary counters; it does not establish scratch-zero reachability at macro calls. Clean scratch is inherited through the old macros' clean-to-clean semantic contracts and the ordinary composition argument. The upstream `AXMacro.registers` definition materializes these two zeros; `AXMacro.Realizes` and `AXMacro.Plan.sound` support their preservation in a certified original macro plan. No new certified plan or call-site scratch-zero reachability theorem is supplied for this composition.

## Rejected padding experiment

The all-natural lemma

`A* = I(I(D+1, I(H,D+1)), A) > max(D,H)`

is proved in `theory_results.tex`. The antecedent is a propositional tautology, so the padded formula is logically equivalent to the old property. The `+1` is necessary for the zero-code corner case. This does not establish that the restricted emitted axioms preserve all refutations of the original calculus.

The cheapest allocation retained from this bounded screen had 210 states before validation. It fails the symbolic primitive contract at source ordinal 2,413, after 3,138 successful contracts. No literal table is released as a candidate. The frozen grammar, folds, allocation hash, search budget, and precise rejection are included so that `replay_padded_failure.py` can reconstruct and reject it independently. The historical receipt records a corrected blank-start reachability check; the corrected result has the same count and same failure.

## Provenance and scope

All upstream material is pinned to ProveIt commit `906367250a7f96c923147b10df392294bced7be5`. The two parent archives are recorded in `PROVENANCE.json`, which also hashes every vendored file. Upstream licenses are retained under `vendor/`. The new composition, verifier, arithmetic padding lemma, and rejected allocation record are local research contributions. Search logs describe bounded heuristic screens, not impossibility or optimality proofs.

The companion root package also investigates the H-only exterior. Its 3,444-site direct-negation/diagonal composition is a distinct machine; this packet deliberately retains the independently verified 3,468-site composition with the original exterior.
