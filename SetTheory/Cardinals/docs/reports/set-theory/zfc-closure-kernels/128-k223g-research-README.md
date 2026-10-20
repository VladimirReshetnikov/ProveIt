# Research retained with K223

The complete candidate is specified and verified in `../portable/`.
This directory records related mathematical frontends and bounded searches.
None of the negative searches is a proof that 223 states is minimal.

| Item | Contents and scope |
|---|---|
| `equality_frontends/` | Uniform mathematical arguments and a standard-library driver regenerating nine finite proof certificates. Its README gives the exact modes and assumptions. |
| `source_research_notes.md` | Measured source changes, successful source sharing, the seven-zero failure and repair, and the costs of other sound logical rows. |
| `table_research_notes.md` | Scoped contextual-fold and representation searches on the released 224-state table. |
| `table_search_summary.json` | Recorded search counts and hashes of the original exploratory reports. The session-specific search harness is not part of the portable replay. |
| `measurements/` | Selected raw source-layout observations for crossed-helper variants. DAG counts are source measurements, not working-state counts or complete machine certificates. |
| `independent_logic_review.md` | Independent review of the selected G proof, its literal source coverage, and the enumerator's retained contracts. |

## Exploratory proof reproduction

From the root of the extracted packet:

```sh
python3 -B research/equality_frontends/research_reproduce.py --output-dir ../K223-equality-experiments
```

The output directory receives copies of the five companion proof scripts,
the generated proof DAGs, and checked receipts for all nine modes. No
retained proof JSON or external package is needed for this command.

## Raw measurement files

The C1 layout files record the ordinary row retained and omitted,
respectively. The C2 helper file records a related double-quantifier
helper screen. The C2 source screen records 14,300 attempted layouts
with no admissible result; its `best` value `[999,99,99]` is an initial
sentinel, **not an observed machine or source size**. These files are
included as research observations; only the selected G construction
has the complete candidate-specific compiler and runtime replay.
