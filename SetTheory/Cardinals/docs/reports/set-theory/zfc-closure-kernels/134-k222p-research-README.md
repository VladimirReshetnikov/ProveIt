# Supplementary research and limited local fold searches

The positive 222-state constructions, proofs, and executable verification are in `../portable/`. This directory preserves supplementary research and the exact scope of one unsuccessful local search. These searches are not premises of the consistency equivalence or correctness of the delivered machines.

## Which literal tables were searched

`local_folds/` contains the unchanged, self-contained standard-library search program, exact input table copies, and the unchanged `facts.json` and `folds.json` outputs for four searches:

| Search ID | Working states | Constant-bit facts retained | Accepted additional folds |
| --- | ---: | ---: | ---: |
| `g223` | 223 | 559 | 0 |
| `seed223` | 223 | 566 | 0 |
| `conditional223` | 223 | 559 | 0 |
| `seed_g222_intermediate` | 222 | 509 | 0 |

The three 223-state inputs are respectively the incoming merged-G construction, the incoming seed-K construction, and the repository's published conditional-K construction at commit `6ab3e41e4dcddfbd7f843bdf4be48ae5c7ba2430`. `local_folds/provenance.json` identifies every exact table hash, source location or ZIP member, label convention, and output hash. All four inputs use historical K labels, with start 0, dispatcher 84, and halt 254.

**The searched 222-state input is an intermediate table, not the exact delivered primary table.** Its K118/read1 row is `(1,L,211)`; the final primary table uses the equivalent direct continuation `(1,R,153)`. The retained negative search outcomes apply only to the exact input bytes listed in the provenance file. No exact-primary no-fold search receipt is claimed. The intermediate table itself is included as `local_folds/inputs/seed_g222_intermediate.k.tm` so the distinction is directly reviewable.

The searches were performed during construction. Packaging copied the original script and receipts unchanged and recorded their input hashes; it did not rerun any search. The facts files and empty fold lists are outputs of the supplied exploratory program, not independent proof-assistant certificates.

## Search model and limitations

The program first propagates a conjunction of known tape-bit facts in offsets -8 through 8 around the head. It starts with no tape restrictions at state 0, so the facts are intended as inductive overapproximations for arbitrary initial binary tapes. The abstraction keeps constant bits, discarding correlations between unknown bits and other nonlocal information.

For each candidate pair of noninitial working states, the search synthesizes the two retained rows. Its first action ranges over either written bit, either direction, and an existing working-state target. Subsequent paths follow the original table and must reach the exact old one-step endpoint, preserving the head position and complete tape at that boundary. Every accessed tape cell must have a known value in the available finite patch. The final candidate block check allows at most 20 transitions.

The implementation imposes further restrictions. It excludes pairs where an old outgoing row targets either merged state, and its precomputed replacement paths may not pass through either merged state internally. It retains the lower numerical label, permits no head-offset representation, and does not synthesize new auxiliary states or an alternative source program. It reports whether a single fold exists within this restricted model.

Consequently the four empty fold lists establish only that this particular bounded local search found no accepted fold for those four tables. They do not establish a lower bound on state count, exhaust all one-state simulations, or exclude reductions using relational tape invariants, longer paths, simultaneous folds, neutral rewrites followed by folds, different compiler layouts, or a different equiconsistent formalism. In particular, simultaneous multi-state transformations were not searched.

## Reproduce a recorded exploratory search

From the packet's top directory, with Python 3.10 or later and an output directory whose parent already exists:

```sh
python3 -B research/local_folds/search_folds.py \
  research/local_folds/inputs/seed223.k.tm \
  /tmp/k222-seed223-fold-search
```

The script writes `facts.json` and `folds.json` to the requested directory. This is an optional exploratory rerun, separate from `portable/reproduce.py`. The negative observations should be compared to the corresponding exact input hash in `local_folds/provenance.json`.

## Binder and parenthesization measurements

`binder_probe.py` reproduces the six measurements in `binder_measurements.json` using only the pinned inputs in `../portable/`. It first undoes the primary construction's successful closed address-repair rotation, then varies the numerical binder constructor and the local parenthesization of the merged equality emitter. The table therefore measures exploratory, unrepaired source layouts; its Rel control has a seven-zero address even though the delivered primary source has a six-zero maximum.

| Binder constructor | Local association | Distinct source subtrees | Primitive occurrences | Maximum zero run |
| --- | --- | ---: | ---: | ---: |
| Rel | Left | 208 | 4,744 | 7 |
| Rel | Right | 208 | 4,744 | 7 |
| Eq | Left | 208 | 4,746 | 7 |
| Eq | Right | 208 | 4,746 | 8 |
| All | Left | 210 | 4,745 | 7 |
| All | Right | 210 | 4,745 | 6 |

These are source-size measurements only. The probe constructs no literal binary machine, proves no runtime certificate, and makes no consistency-equivalence claim for these six variants. A smaller or equal subtree count alone does not determine a working-state count:address requirements and contextual decoder aliases must also be checked. These six local variations are not an exhaustive search over binder choices or source grammars.

Run from the packet's top directory:

```sh
python3 -B research/binder_probe.py > /tmp/k222-binder_measurements.json
```

## Independent mathematical audit

`independent_seed_g_audit.md` reviews why the root-independent G replacement composes with the seed theory, handles the exact emitted bundle order, avoids circular equality reasoning, preserves the inherited native-code edge cases, and supports the two literal folds. Its corresponding executable checkers and receipts are included in `../portable/`. The audit distinguishes ordinary mathematical correctness from a new proof-assistant endpoint and retains the inherited calibration dependencies.
