# Current PA-machine comparison

Pinned ProveIt commit: `3cc7fbf75ba111a0da696ef2f6001dd528891bd5`.

## Deliverable inputs

- `packet_ledger.csv`, `.json`, `.md`: all 47 placed packets plus four incoming submissions.
- `frontier194.csv`, `.json`, `.md`: all 34 recognized 194-state graph classes, evidence classifications, changes, and source locators.
- `frontier_tables/`: one exact literal representative per 194-state graph class.
- `census.json`: fresh complete numeric-table inventory, nested archive identities, byte and graph identities, source locators.
- `placed_class_reconciliation.json`: maps every one of the repository's 481 recorded classes to the fresh census; explains the three synthetic reachable-subgraph classes and nine new whole-table classes.
- `inventory_census.py`: inherited parser/canonical traversal, freshly rerun; attributed to the supplied PA194N6 packet.
- `check_novelty.py`: new exact-tuple comparison against the 34 graph representatives. Allows renaming, root choice, reflection, and global bit exchange.
- `novelty_positive_control.json`: confirms that PA194HS matches PA194NS.
- `../report/main.tex`: complete comparison and proof-boundary discussion.

The corpus has 1,811 recognized numeric-table occurrences, 683 byte identities,
487 whole-table spanning-root graph classes; at 194 states, 208 occurrences,
62 byte forms, and 34 classes. The 194-state evidence labels consist of 21
supplied mathematical/physical designs, nine auxiliary tables, and four
rejected experiments. They describe prior claims, not newly replayed proofs.

The scan inspects every file under PA and every incoming archive, recursively
visiting each distinct nested ZIP payload once. Numeric literal tables in
`.tm`, `.txt`, `.tsv`, and `.csv` are recognized. Arbitrary machines encoded
only in JSON, code, or prose are outside that automatic count. The narrative
ledger separately accounts for every packet.

## Duplicate corrections

PA194C appears in five packet deliveries. PA194X equals PA194CSZ. The incoming
PA194NS equals PA194HS byte for byte, and both N6 submissions give the same
N6 bytes. These do not represent four additional independent results.

## Exploratory MP tails

`../research/mp_tails/` is separate unsuccessful source-cost research, not an accepted
194-state theorem. Its `replay.py` builds two alternative successful-MP
tails using the original Shift controller. One returns `(b,w,0,0)` and another
returns `(b,w,0,b)`. Both physical constructions have 195 working states and
pass the inherited universal source checks and exact startup. The new reader
cannot be folded directly by the searched three-step context template.
Further bounded single-row synthesis is recorded separately. No logical
consistency calibration or independent literal runtime audit is claimed for
these 195-state exploratory machines.
