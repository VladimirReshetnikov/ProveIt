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

The `packet` and `file` columns name files under `Analysis/GeneralizedRiemannHypothesis/Research/`
in the history (the first 103 at commit `10802a6b36`, the next 17 at commit `f2f9fd7531`, the next 11 at commit `64f3896557`, the next 11 at commit `fd9a9cb2bd`, the next 42 at commit `f6b5955e13` and the last 10 at commit `7f951e1dfd`); the packets are no longer in the working tree.

Labels have the form `<key>:<kind>:<name>`, and `<key>` names the section file. The
`conflict` rows mostly concern how the reports describe the upstream proof; the article
uses the latest, corrected description.

| Table | `merged` | `duplicate` | `subsumed` | `answered` | `conflict` | `other-unit` | `non-mathematical` | Rows |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| [`src.tsv`](src.tsv) | 68 | 90 | 5 | 0 | 9 | 28 | 53 | 253 |
| [`ana.tsv`](ana.tsv) | 137 | 19 | 18 | 5 | 1 | 20 | 28 | 228 |
| [`li.tsv`](li.tsv) | 91 | 8 | 5 | 2 | 0 | 10 | 16 | 132 |
| [`nab.tsv`](nab.tsv) | 42 | 3 | 11 | 2 | 0 | 32 | 19 | 109 |
| [`grp.tsv`](grp.tsv) | 72 | 4 | 7 | 3 | 0 | 14 | 8 | 108 |
| [`hec.tsv`](hec.tsv) | 60 | 11 | 6 | 0 | 0 | 14 | 5 | 96 |
| [`zer.tsv`](zer.tsv) | 158 | 13 | 14 | 6 | 0 | 47 | 44 | 282 |
| [`rec.tsv`](rec.tsv) | 290 | 50 | 34 | 7 | 0 | 27 | 43 | 451 |
| [`fil.tsv`](fil.tsv) | 75 | 14 | 14 | 5 | 0 | 11 | 14 | 133 |
| [`dir.tsv`](dir.tsv) | 243 | 35 | 13 | 5 | 2 | 39 | 74 | 411 |
| [`cls.tsv`](cls.tsv) | 23 | 7 | 11 | 5 | 0 | 20 | 6 | 72 |
| [`smd.tsv`](smd.tsv) | 57 | 13 | 23 | 8 | 0 | 16 | 5 | 122 |
| [`gpp.tsv`](gpp.tsv) | 55 | 3 | 8 | 6 | 0 | 0 | 6 | 78 |
| [`gpi.tsv`](gpi.tsv) | 39 | 10 | 13 | 7 | 0 | 24 | 7 | 100 |
| [`gra.tsv`](gra.tsv) | 74 | 11 | 4 | 6 | 0 | 15 | 3 | 113 |
| [`tors.tsv`](tors.tsv) | 51 | 2 | 9 | 4 | 0 | 10 | 3 | 79 |
| [`cost.tsv`](cost.tsv) | 64 | 13 | 7 | 8 | 0 | 10 | 9 | 111 |
| [`lub.tsv`](lub.tsv) | 72 | 12 | 11 | 4 | 0 | 8 | 12 | 119 |
| [`sel.tsv`](sel.tsv) | 64 | 16 | 5 | 4 | 2 | 8 | 10 | 109 |
| [`spn.tsv`](spn.tsv) | 213 | 51 | 21 | 10 | 0 | 6 | 35 | 336 |
| [`corpus.tsv`](corpus.tsv) | 0 | 0 | 2 | 0 | 0 | 0 | 46 | 48 |
| Total | 1948 | 385 | 241 | 97 | 14 | 359 | 446 | 3490 |

`corpus.tsv` covers the source files that no section table names: bibliographies, layout
files, main files that hold only a title, an abstract and the list of included files,
inventories of earlier reports, verification records, and two tables comparing superseded
bounds. With it, every `.tex` file of every report has at least one row.

194 of the 194 reports appear in at least one table with a disposition other than
`other-unit`.
