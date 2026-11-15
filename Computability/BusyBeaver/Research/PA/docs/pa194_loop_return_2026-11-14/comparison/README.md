# Current comparison and exact novelty replay

Pinned ProveIt commit: `8d31445d858761a8f6150c2e5012adae8895e932`.

## Counts and scope

| Quantity | Count |
|---|---:|
| Filed research deliveries | 87 |
| Current incoming ZIP deliveries | 6 |
| Selected tracked payloads scanned | 13,934 |
| Distinct recursively inspected ZIP payloads | 24 |
| References to those ZIP payloads | 39 |
| Recognized physical 194-state occurrences | 1,988 |
| Normalized labeled 194-state tables | 232 |
| Spanning 194-state action-graph classes | 139 |
| Additional nonspanning 194-state encodings | 2 |
| Named principal/supplementary 194-state constructions | 74 |
| Spanning 193-state research classes | 54 |
| Official 194-state classes matched | 110 of 110 |
| Read/parse errors | 0 |

The 139 classes include research and rejected tables. The 74 named constructions are attributed designs with different proof statuses; they are not 74 independently verified iPRA calibrations. No 193-state consistency theorem follows from the inventory.

Compared with the filed 110-class frontier, the six current archives add 11 named designs and 18 other graphs: seven rejected loop/scanner compositions, ten selector research inputs and one append-zero input. The named roster is grouped into 26 mechanism families. The full delivery ledger contains all 93 packets.

## Files

`all_194_classes.csv` describes every spanning 194-state class. `named_194_designs.csv`, `families.csv` and `packet_ledger.csv` give the named mechanisms, exact starts, proof-status distinctions and delivery comparison. Corresponding JSON files preserve the same data.

Source bytes and archive identities are recorded in `source_payloads.json`; source occurrences for every retained prior 194-state table are bound in `novelty_manifest.json`. Unknown starts on auxiliary graphs remain unknown. Named starts are bound to particular verified table presentations.

## Offline novelty verification

Run:

```sh
python3 verify_novelty.py --output fresh_novelty.json
```

The script checks both final candidate tables and all 232 retained labeled tables. For every comparison it emits an exact differing multiplicity in the structural histogram of

`(working indegree, self-loop row count, equal-successor indicator)`.

This histogram is invariant under working-state renaming, a change of designated start, tape reflection, global symbol exchange and terminal-edge action erasure. Hashes check file identity; they do not decide graph nonisomorphism.

The final pair is separated by 86 versus 85 controls with profile `(1,0,0)`. Neither candidate profile equals any prior profile, including the two nonspanning diagnostics. This establishes structural novelty independently of the correctness and consistency-calibration arguments.

## Repeating the source enumeration

With the pinned Git objects available:

```sh
python3 census_tools/current_frontier.py /path/to/ProveIt 8d31445d858761a8f6150c2e5012adae8895e932
```

This writes `census_tools/frontier/`. The scanner recognizes complete numeric five-column tables, documented JSON row/action encodings and embedded whole-table strings, recursively through ZIPs. It does not execute arbitrary generators, infer tables from prose or decode opaque binary formats. Every tracked payload's Git blob hash is checked against the pinned tree. Large JSON uses a bounded-retention walker for the same explicit table shapes. The enumeration script uses Unix resource controls; the offline novelty replay uses only portable Python standard-library modules.

## Attribution

The literal/JSON recognizers are adapted from the supplied PA q-radix research and AX11GH companion census. `machine_classes.py` is the supplied repository classifier. Existing mechanisms, names and attributed proof statuses are inherited and reconciled against the current source. Current additions are the complete present-snapshot scan, resolved named starts, deduplication, metadata and exact invariant novelty certificates. Retain the upstream ProveIt, James Chang and Wade notices with the enclosing research package.
