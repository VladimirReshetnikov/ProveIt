# Provenance tables

One tab-separated table per section of the [merged article](../README.md), with the columns
`packet`, `file`, `section`, `disposition`, `target` and `note`. A row names a section of a
report (or one result in it) and says what happened to it:

| Disposition | Meaning |
|---|---|
| `merged` | Its mathematics is in the article; `target` is the label that holds it. |
| `duplicate` | Another report proves the same result; `target` is the label kept. |
| `subsumed` | It follows from a stronger or more general result; `target` is that result, and `note` says why it is stronger. |
| `answered` | It is a question that another report answers; `target` is the answer. |
| `conflict` | Reports disagree; `note` says how, and which version the article uses. |
| `other-unit` | It belongs to another section; `target` is that section's key. |
| `non-mathematical` | Audits, inventories of earlier reports, reproduction and formalization plans, and similar material, which the article leaves out. |

Labels have the form `<key>:<kind>:<name>`, and `<key>` names the section file. The
`conflict` rows mostly concern how the reports describe the upstream proof; the article
uses the latest, corrected description.

| Table | `merged` | `duplicate` | `subsumed` | `answered` | `conflict` | `other-unit` | `non-mathematical` | Rows |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| [`src.tsv`](src.tsv) | 68 | 90 | 5 | 0 | 9 | 28 | 53 | 253 |
| [`ana.tsv`](ana.tsv) | 118 | 19 | 17 | 4 | 1 | 20 | 21 | 200 |
| [`li.tsv`](li.tsv) | 73 | 9 | 2 | 1 | 0 | 10 | 13 | 108 |
| [`nab.tsv`](nab.tsv) | 42 | 3 | 11 | 2 | 0 | 32 | 19 | 109 |
| [`grp.tsv`](grp.tsv) | 72 | 4 | 7 | 3 | 0 | 14 | 8 | 108 |
| [`hec.tsv`](hec.tsv) | 60 | 11 | 6 | 0 | 0 | 14 | 5 | 96 |
| [`zer.tsv`](zer.tsv) | 145 | 12 | 12 | 5 | 0 | 47 | 41 | 262 |
| [`rec.tsv`](rec.tsv) | 268 | 26 | 16 | 7 | 0 | 20 | 31 | 368 |
| [`dir.tsv`](dir.tsv) | 122 | 10 | 5 | 3 | 2 | 39 | 13 | 194 |
| [`cls.tsv`](cls.tsv) | 23 | 7 | 11 | 5 | 0 | 20 | 6 | 72 |
| [`smd.tsv`](smd.tsv) | 30 | 7 | 21 | 5 | 0 | 16 | 1 | 80 |
| [`gpp.tsv`](gpp.tsv) | 55 | 3 | 8 | 6 | 0 | 0 | 6 | 78 |
| [`gpi.tsv`](gpi.tsv) | 39 | 10 | 13 | 7 | 0 | 24 | 7 | 100 |
| [`gra.tsv`](gra.tsv) | 49 | 8 | 1 | 4 | 0 | 15 | 2 | 79 |
| [`tors.tsv`](tors.tsv) | 50 | 2 | 7 | 3 | 0 | 10 | 3 | 75 |
| [`cost.tsv`](cost.tsv) | 52 | 10 | 7 | 7 | 0 | 10 | 6 | 92 |
| [`lub.tsv`](lub.tsv) | 57 | 9 | 9 | 3 | 0 | 6 | 6 | 90 |
| [`sel.tsv`](sel.tsv) | 64 | 16 | 5 | 4 | 2 | 8 | 10 | 109 |
| [`spn.tsv`](spn.tsv) | 173 | 30 | 12 | 5 | 0 | 6 | 28 | 254 |
| [`corpus.tsv`](corpus.tsv) | 0 | 0 | 2 | 0 | 0 | 0 | 46 | 48 |
| Total | 1560 | 286 | 177 | 74 | 14 | 339 | 325 | 2775 |

`corpus.tsv` covers the source files that no section table names: bibliographies, layout
files, main files that hold only a title, an abstract and the list of included files,
inventories of earlier reports, verification records, and two tables comparing superseded
bounds. With it, every `.tex` file of every report has at least one row.

142 of the 142 reports appear in at least one table with a disposition other than
`other-unit`.
