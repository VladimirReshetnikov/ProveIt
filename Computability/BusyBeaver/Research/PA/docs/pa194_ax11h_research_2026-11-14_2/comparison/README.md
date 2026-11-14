# Comparison scope and replay

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `1c9524d8bf2e0a27b9a16ff622359927f536e663`.

This directory records an exhaustive inventory of **recognized literal and explicit JSON tables** in the pinned PA tree and incoming ZIP payloads. It does not execute every possible generator to infer an unprinted table, and it does not independently re-prove every historical calibration. Source-only proposals and the principal operational mechanisms are reviewed in the report; for example, QAX11 without H was already an exploratory source seed and is not claimed here as new.

## Files

- `delivery_ledger.json` and `.csv`: all 61 filed plus 11 incoming deliveries, with reported contribution, source paths, readme identities, and scope notes.
- `frontier194.json` and `.csv`: all 82 recognized spanning 194-state classes, with attributed mechanism, historical evidence category, full graph identifier, and all occurrence paths.
- `census/census.json`: complete raw census, including source Git-blob checks, archive provenance, literal/JSON occurrences, normalized table identities, and graph classes.
- `census/summary.json`: exact aggregate counts and parser error list.
- `census/frontier_tables/`: one table for each of the 82 classes plus the two recognized 194-state normalized identities with no spanning root.
- `novelty_PA194AX11H.json` and `novelty_PA194QAX11H.json`: candidate comparisons against the whole recognized 194-state set.
- `scanner/`: attributed recognizers and the current census and novelty wrappers.

The historical evidence categories (principal, supplementary, source-validated rotation, auxiliary, rejected) describe the supplied reports. They are not a certification of an iPRA consistency theorem. The report and pinned upstream README state the exact proof boundary.

## Counts

The current scan verified 10,171 tracked candidate files and inspected 15,220 file/member payloads. It found 3,422 table occurrences, 752 normalized table identities, 638 spanning graph classes, and six identities without a spanning root. There are 82 spanning classes at 194 states, and two additional 194-state identities without a spanning root. Thirty-five one-state JSON fragments are excluded; `errors` is empty.

The earlier repository catalog has a different scope: literal `.tm` files and an older incoming set. Its 49-class figure at 194 states should not be compared with 82 as if both counted the same input corpus.

## Reproduce the current census

Obtain a checkout of the exact commit, including both requested directories, then run:

```sh
python3 -B comparison/scanner/audit_current.py --repo /path/to/ProveIt --output /tmp/pa-current-census
```

The scanner asserts the commit identity and verifies relevant tracked-file bytes against Git blobs before using them. It recursively reads incoming archives and explicit JSON transition tables. Use a new output directory. The two extra nonspanning representatives in this release were retained from the resulting normalized identities; their lack of a spanning root is independently checked during novelty replay.

## Reproduce a novelty comparison

```sh
python3 -B comparison/scanner/compare_novelty.py machines/PA194AX11H/machine.tm comparison/census/frontier_tables --output /tmp/ax11h-novelty.json
```

Repeat for QAX11H. The algorithm compares complete canonical tuples, permitting arbitrary state renaming, every spanning root, tape reflection, symbol complement, and any terminal halt-edge write/movement. A symbol complement is used as a broad structural novelty test; it is not asserted to preserve the designated all-zero initial tape without changing the blank convention. No candidate matches, and their distinct canonical tuples also distinguish them from each other. The two nonspanning tables are excluded by an invariant preserved under these transformations.

These checks establish novelty relative to recognized tables in the pinned corpus. They do not assert global historical novelty or inequivalence under arbitrary program transformations.
