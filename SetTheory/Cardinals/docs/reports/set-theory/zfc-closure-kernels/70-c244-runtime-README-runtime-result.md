# A verified 244-state reduction of Routing245

The recommended result is `candidate_1_244.tm`: a binary, two-way, one-tape
Turing machine with 244 working states, start state 0, and target-only halt
state 244. The bijective old-label table is `candidate_1_244_old.tm`, with
start 95 and halt 254.

The construction has a direct mathematical proof of the same halting outcome
as Routing245, started in state 95 on **every initial binary tape**. In
particular, the blank-tape consistency calibration transfers from Routing245.
The new proof uses an inductive condition on one or two nearby tape cells and
seven exact finite transition identities. It does not assume a register frame,
a source-program path, a sufficiently large gap, or bounded register values.

## The exact change

Delete old state 122 and change these four retained rows:

| State/read | Old row | New row |
|---|---|---|
| 92/1 | `1 L 24` | `1 R 66` |
| 104/1 | `1 R 122` | `1 R 92` |
| 106/1 | `1 R 122` | `1 R 92` |
| 167/1 | `1 L 92` | `1 L 151` |

The 128 allocated grammar states remain present. The framework decreases from
117 to 116 states. The state fold uses information that the incoming
transitions leave on the tape; the rerouting through 151 preserves a context
that would be damaged by the uncorrected merge.

## Proof artifacts

- `../proof/contextual_fold.tex` contains the complete global simulation proof.
- `prove_contextual_fold.py` checks the exact patch, all incoming edges needed
  for the invariant, all local Boolean implications, and every finite window
  identity. It refuses to inspect tape outside the declared finite window.
- `contextual_fold_proof.json` records the checked facts: 7,784 invariant
  implications, 482 common one-step rows, and seven exceptional window cases.
- `candidate_1_full_symbolic.json` is an additional complete all-values runtime
  replay: 8,391 guarded cases, 2,315,075 symbolic rules, all 488 transition rows,
  and positive progress with a minimum of 13 steps. It uses the inherited
  unmodified whole-frame verifier.
- `candidate_1_boot.json` records independent sparse/dense agreement after
  exactly 407,951 blank-tape steps. The resulting complete root frame is
  identical to the Routing245 root frame: head -5, header 176, physical values
  `(0,0,0,3,0,0,3,0,0)`, 167 spare values equal to 1, and 351 one-cells.

The local and whole-frame Python checkers are mathematical proof checkers,
not new Lean or Rocq kernel endpoints. Their finite checks are accompanied by
the explicit induction and bounded-stuttering argument in the TeX proof.

## Reproduction

Run the following commands from the `runtime/` directory. Python 3 and its
standard library suffice for the principal result:

```sh
python3 rebuild_candidates.py
python3 prove_contextual_fold.py
python3 check_new_boot.py candidate_1_244_old.tm candidate_1_boot.json
```

To replay the additional universal register-frame proof, allow several minutes:

```sh
python3 code/full_symbolic_parametric.py \
  --table candidate_1_244_old.tm --all-values \
  --sites certificate/sites_physical.json \
  --output candidate_1_full_symbolic.json
```

The full verifier, its source parser, induction checker, original source, and
invariant certificate are copied without modifications under `code`,
`reference/context246`, `certificate`, and `results`. The one-case
`portability_smoke.json` checks those local dependencies; the full 8,391-case
certificate is the separate complete proof run on the same bytes.

`rebuild_candidates.py` also produces two additional 244-state tables that
passed every full-frame and blank-tape obligation. Candidate 2 deletes old
state 149 and repairs 167/1. Candidate 3 deletes 149 and repairs 170/1.
Candidate 1 is preferred because its global finite-context proof is smallest
and has been independently reviewed.

## Discovery search and its scope

`merge_plus_compensation.cpp` extends the previously unsuccessful pair-merge
family by permitting one additional row change. It first selects the 54 pair
merges that passed the original quick probes, then tests a compensating row on
the actual trace of a failed instruction. All possible writes, directions,
and retained state targets are considered for each selected repair location.

The run tested 6,032,656 compensation choices. Of these, 18,816 passed the
first failed case and 42 passed the expanded quick probes. Exactly three
passed all 8,385 complete finite instruction fixtures. These are the three
tables above. `repair_summary.json`, `repair_seeds.txt`,
`repair_survivors.txt`, and `merge_plus_compensation.log` record the search.

The finite search admits a translated safe frame and arbitrary nonempty spare
values, with the same instruction result and primary values. It uses fuel
6,000 in the repair screen and 20,000 for the full fixture screen; tape cells
range from -64 through 1983. It is a search over one selected family, not a
lower bound or a completeness theorem for all state reductions. The global
simulation proof and the universal runtime checks supply the result's proof;
search success by itself is not used as a universal premise.

To replay the optional search, decompress `reference/cases.txt.gz`, compile
the C++17 source, and supply that fixture as its first argument. The compiled
binary and decompressed fixture are scratch outputs and need not be shipped.

## Digests

| Table | SHA-256 |
|---|---|
| Original Routing245, old labels | `f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267` |
| Recommended 244-state table, old labels | `d603bc3793ac9373f510a05d4e898f4ee7b4cac492821406a665554dca5c6daf` |
| Recommended 244-state table, canonical labels | `2ea5521fa7d0fc24b4f3dc07d497b10de2532147225820033d9c96f247444187` |

Inherited machine, proof-checker, and search-replay code is attributed to its
original authors in `reference/NOTICE-routing245.txt` and the preserved
license files. The compensated merge search, exact 244-state candidates,
finite-context proof, and new replay scripts were prepared for this
investigation on 18 October 2026.
