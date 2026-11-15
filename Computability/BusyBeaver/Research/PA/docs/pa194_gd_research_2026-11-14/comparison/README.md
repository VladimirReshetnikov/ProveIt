# Comparison scope and portable representatives

All counts refer to ProveIt revision
`8d31445d858761a8f6150c2e5012adae8895e932`.

- `filed_packets87.*`: all 87 filed delivery descriptions, with reported
  mathematical and implementation mechanisms attributed to their sources.
- `historical_designs110.*`: the 110 spanning structural classes found among
  the 111 tracked 194-state tables. Categories include rejected and diagnostic
  experiments; this is not a list of 110 proved consistency machines.
- `pending_principal_designs11.*`: eleven additional principal graph classes
  in the six pending ZIPs. Seventeen principal delivery occurrences collapse
  to these eleven classes.
- `frontier194.json`, `frontier194.csv`, and `frontier194/`: all 139 prior
  spanning 194-state classes, including eighteen further pending auxiliary
  or rejected classes. Each `representative` path resolves from this directory.
- `recursive_census.json` and `recursive_summary.json`: complete literal-table
  recognizer results, exclusions, nested archive locators, and count summaries.
- `archive_provenance.json`: identities of the six pending archives.

`representative_file`, `source_table`, and occurrence `path` fields retain
their original upstream/archive-relative provenance. They are not promises
that all original delivery directories are copied here. The added
`packaged_representative` fields in the historical and pending ledgers point
to this packet's corresponding `frontier194/` representative. Structural
equivalence can identify byte-distinct representatives, so the original
`representative_sha256` remains the identity of the original source bytes.

The exact comparison permits arbitrary state renaming, any spanning root,
tape reflection, symbol exchange, and terminal-action erasure. Full tuples
are compared, not only hashes. Allowing symbol exchange is a stronger graph
novelty screen, not a claim that it preserves the all-zero initial tape.
Run the new-machine comparison from the packet root:

```sh
python3 -B verification/independent/check_novelty.py
```

For a fresh census of the original repository, supply **the 718 tracked PA
`.tm` files explicitly** and the six pending ZIPs to `census_tables.py`.
Passing the whole PA directory would also recursively expand six older filed
ZIPs, changing the scope of the reported 2,826-occurrence census. See the
program's `--help` for its input/output options. Only literal five-column
transition tables are recognized; arbitrary generators, prose, and tables
stored exclusively in other encodings are not automatically reconstructed.

The graph census is exhaustive within that stated recognizer and snapshot.
The semantic ledger does not claim an independent rebuild of all 93
deliveries' arithmetic proofs. Newly replayed operational results are listed
separately in the main report and verification receipts.
