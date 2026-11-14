# Pinned comparison and novelty replay

Repository revision: `32d0d8b7d93a63ad4106c18cdb29b37927acdad2`.

`comparison_notes.md` explains the architecture, duplicate names, proof status, and precise count reconciliation. `named_designs.csv`/`.json` compare all 58 named 194-state designs; `named_designs.tex` is the report appendix. `packet_ledger.csv`/`.json` cover all 82 deliveries. `frontier194.csv`/`.json` identify every one of the 94 current spanning 194-state action graphs, including auxiliary and rejected entries, and preserve source/start metadata.

The final census has no missing selected inputs: 10,090 pinned files, 12,461 inspected payloads, 3,594 recognized table occurrences, 778 labeled identities, and 658 spanning one-terminal graph classes. Ninety-four classes have 194 working controls. Counts do not imply that every graph has a consistency calibration. The recognized input formats and exclusions are documented in `audit.py` and the notes.

## Offline novelty replay

The 94 reference tables are under `census_full/tables`. Python 3 and its standard library suffice:

```sh
python3 verify_novelty.py --references census_full/tables \
  --output fresh_novelty.json /path/to/PA194GH/machine.tm /path/to/PA194GHS/machine.tm
```

The checker compares full canonical tuples under every spanning root, arbitrary control renaming, reflection, global bit exchange, and ignored terminal write/move effects. It also checks the simpler indegree-histogram certificate and computes the greatest immediate-action control congruence. The bit exchange is an enlarged structural exclusion test; it is not claimed to preserve a zero-blank semantic convention. The congruence test is not a global state lower bound.

`novelty_pair.json` records the run against these exact final representatives. The earlier `novelty_pair_literal_references.json` used the same 94 graph classes with possibly different native/dense representative numbering. Both candidate starts are zero by their explicit design convention; graph reachability from that start covers all 194 controls.

Two disconnected diagnostic tables are retained separately under `nonspanning194`, with their invariant in `nonspanning194.json`. Neither has a spanning root; the maximum reachable working-control count is three. They cannot be isomorphic to either candidate.

## Full census replay

Given a Git checkout containing the pinned file blobs:

```sh
python3 audit.py --repo /path/to/ProveIt --output /new/census \
  --candidate /path/to/PA194GH/machine.tm
```

The scanner is read-only and does not fetch absent promisor objects. It verifies Git blob identities, reports missing objects, and fails if any selected tracked blob is absent or an archive cannot be opened. It records unrecognized diagnostic/fixed tables separately. Arbitrary generators and proof texts are not executed.

The human annotation tables can be reconstructed from the retained pinned input indexes with `python3 build_comparison.py`. Their role labels attribute the source reports; the mathematical proofs of every historical candidate were not re-run. `command_review.md` records the independent review of the new GH command argument and its weak-arithmetic boundary.

Project/upstream licenses, source attribution, and the exact historical indexes are retained alongside the comparison. `PROVENANCE.json` identifies the source roles of imported descriptive metadata and new audit code.
