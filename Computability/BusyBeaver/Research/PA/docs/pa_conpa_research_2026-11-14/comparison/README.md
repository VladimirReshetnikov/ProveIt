# Pinned corpus comparison

This directory is a self-contained structural comparison and replay package for ProveIt revision `1e1a41f799d4658b829cdd0eabae3775a0c8c4a0`. It attributes historical mathematical claims and does not turn a transition-table census into a proof of arithmetic correctness.

## Offline novelty replay

From the release root:

```sh
python3 comparison/check_novelty.py
```

By default this compares `machines/PA194AX11GH/machine.tm` and `machines/PA194AX11GHS/machine.tm` to every supplied historical representative. It writes a receipt to a fresh temporary directory. Paths can also be provided explicitly:

```sh
python3 comparison/check_novelty.py path/to/first.tm path/to/second.tm --receipt /tmp/novelty-replay.json
```

The frozen result is `new_candidates_novelty.json`: zero matches for both candidates against 110 spanning classes; the one nonspanning diagnostic is excluded by its inability to admit a spanning root. The candidates also differ from each other. Complete tuple comparisons allow all spanning roots, state renaming, reflection, global bit exchange, and arbitrary terminal write/move effects. Bit exchange is a strengthened structural comparison, not a claim to preserve an all-zero blank run.

## Inventory and scope

- `packet_ledger86.csv` / `.json`: all 82 filed and four current incoming delivery payloads.
- `comparison194_complete.csv` / `.json`: all 111 historical 194-state table classes, representative locators, hashes, evidence categories and mechanisms.
- `representatives194/`: every representative, including rejected and diagnostic graphs.
- `comparison.md`: mathematical and architectural interpretation, duplicate names, exact proof-status distinctions and promising directions.
- `literal194_summary.json` and `supplement_summary.json`: original fresh component scan receipts.
- `census_replay/`: unified pinned-Git replay, including file/blob manifest, exact recognized occurrences, archive coverage, and result.
- `canonical_tuples194.json` and `canonical_records194.json`: complete frozen canonical tuples and metadata.
- `historical_named_designs.md` and `historical_comparison_narrative.md`: unchanged attributed earlier comparison sources. Their older snapshot counts must not replace the current counts.

The unified replay verifies 13,109 source files against pinned Git blobs, including 18 distinct ZIP payloads through 30 references. Its complete 194-state slice is 908 occurrences and 111 classes (110 spanning and one disconnected).

The recognizers cover complete binary one-halt `.tm`, `.txt`, `.tsv`, and `.csv` matrices, supported explicit JSON tables, and recursively nested ZIP members. They do not execute arbitrary generators or recover transition tables printed only in prose. The complete JSON recognizer handles row arrays, pairs of action triples, flat action arrays, numeric-state dictionaries, transition-key dictionaries, row records, and embedded full text. Counts describe this stated recognition scope.

The table-class inventory forgets the intended start only to compare graph structure. All semantic claims still require the packet's designated start. Contiguous state labels alone are insufficient evidence of a correct start.

## Optional complete source rescan

The bundled representatives suffice for the offline novelty replay. To independently reconstruct the current historical census, provide a local Git checkout of the exact pinned revision with every relevant file materialized:

```sh
python3 comparison/rebuild_census.py --source /path/to/ProveIt --output /tmp/current-pa-census
```

This command verifies every selected file against its pinned Git blob before scanning and refuses a mismatched revision or incomplete sparse checkout. It performs no network retrieval and does not modify the checkout. It checks the recognized class set against the bundled ledger. A failed assertion or a new/missing class is an audit failure; it is not silently omitted.

Python 3.10+ and its standard library suffice. No proof assistant is needed for these structural checks. The parser files under `vendor/` are unchanged pinned inputs, with source locators and hashes in `PROVENANCE.json`; their retained licenses are under `licenses/`.

## LaTeX fragments

`chapter.tex` is a concise comparison chapter. `new_design_position.tex` adds a focused table and concrete command witnesses comparing AX11GH with its nearest predecessors; `reviewer_position.md` is the corresponding concise reviewer note. `frontier_table.tex` prints all 111 class rows, and `packet_table.tex` prints all 86 delivery rows. The latter two can be included after the report's appendix switch. All fragments work with the standard `amsmath`, `amssymb`, `booktabs`, `longtable`, and `hyperref` packages. `generate_tables.py` regenerates the appendices from the frozen JSON ledgers.

```sh
python3 comparison/generate_tables.py
```

The underlying logical calculus, source programs, arithmetic runtime, earlier tables and prior comparisons remain attributed to James Chang, Andrew James Wade, and the ProveIt research contributors. This directory adds the current reconciliation, explicit source coverage, new-candidate structural comparison, and self-contained replay.
