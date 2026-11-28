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
in the history (the first 103 at commit `10802a6b36`, the next 17 at commit `f2f9fd7531`, the next 11 at commit `64f3896557`, the next 11 at commit `fd9a9cb2bd`, the next 42 at commit `f6b5955e13`, the next 10 at commit `7f951e1dfd` and the last 15 at commit `3c4d27a69c`); the packets are no longer in the working tree.

Labels have the form `<key>:<kind>:<name>`. `<key>` names the section file the result was first
merged into; results moved when the article was regrouped on 27 November 2026 kept their labels,
so a label's prefix need not match the file that now holds it. Each table lists the rows whose
target is in its section file. The
`conflict` rows mostly concern how the reports describe the upstream proof; the article
uses the latest, corrected description.

| Table | `merged` | `duplicate` | `subsumed` | `answered` | `conflict` | `other-unit` | `non-mathematical` | Rows |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| [`src.tsv`](src.tsv) | 59 | 97 | 6 | 0 | 9 | 28 | 55 | 254 |
| [`spn.tsv`](spn.tsv) | 45 | 1 | 3 | 1 | 0 | 6 | 47 | 103 |
| [`ana.tsv`](ana.tsv) | 97 | 21 | 20 | 3 | 1 | 20 | 36 | 198 |
| [`li.tsv`](li.tsv) | 72 | 0 | 2 | 1 | 0 | 10 | 16 | 101 |
| [`lih.tsv`](lih.tsv) | 67 | 10 | 4 | 1 | 0 | 0 | 0 | 82 |
| [`nab.tsv`](nab.tsv) | 46 | 4 | 19 | 2 | 0 | 32 | 19 | 122 |
| [`grp.tsv`](grp.tsv) | 66 | 0 | 1 | 3 | 0 | 14 | 8 | 92 |
| [`hec.tsv`](hec.tsv) | 57 | 11 | 1 | 0 | 0 | 14 | 5 | 88 |
| [`zer.tsv`](zer.tsv) | 46 | 2 | 2 | 1 | 0 | 47 | 55 | 153 |
| [`flu.tsv`](flu.tsv) | 77 | 8 | 7 | 5 | 0 | 0 | 0 | 97 |
| [`fil.tsv`](fil.tsv) | 137 | 21 | 19 | 11 | 0 | 11 | 16 | 215 |
| [`rec.tsv`](rec.tsv) | 107 | 4 | 7 | 2 | 0 | 27 | 46 | 193 |
| [`chz.tsv`](chz.tsv) | 116 | 19 | 10 | 3 | 0 | 0 | 0 | 148 |
| [`cpl.tsv`](cpl.tsv) | 71 | 8 | 16 | 4 | 0 | 0 | 0 | 99 |
| [`eul.tsv`](eul.tsv) | 53 | 27 | 24 | 5 | 0 | 0 | 0 | 109 |
| [`dir.tsv`](dir.tsv) | 43 | 6 | 1 | 0 | 2 | 39 | 76 | 167 |
| [`prd.tsv`](prd.tsv) | 176 | 31 | 11 | 6 | 0 | 0 | 0 | 224 |
| [`cls.tsv`](cls.tsv) | 32 | 7 | 11 | 5 | 0 | 20 | 6 | 81 |
| [`cmf.tsv`](cmf.tsv) | 27 | 1 | 2 | 1 | 0 | 0 | 0 | 31 |
| [`smd.tsv`](smd.tsv) | 80 | 14 | 25 | 9 | 0 | 16 | 5 | 149 |
| [`gpp.tsv`](gpp.tsv) | 57 | 4 | 7 | 8 | 0 | 0 | 6 | 82 |
| [`gpi.tsv`](gpi.tsv) | 37 | 9 | 14 | 5 | 0 | 24 | 7 | 96 |
| [`gra.tsv`](gra.tsv) | 69 | 9 | 3 | 5 | 0 | 15 | 3 | 104 |
| [`grw.tsv`](grw.tsv) | 33 | 3 | 1 | 1 | 0 | 0 | 0 | 38 |
| [`cmp.tsv`](cmp.tsv) | 217 | 47 | 19 | 11 | 0 | 0 | 0 | 294 |
| [`tors.tsv`](tors.tsv) | 59 | 12 | 9 | 8 | 0 | 10 | 3 | 101 |
| [`cost.tsv`](cost.tsv) | 75 | 3 | 7 | 5 | 0 | 10 | 9 | 109 |
| [`lub.tsv`](lub.tsv) | 72 | 12 | 11 | 4 | 0 | 8 | 12 | 119 |
| [`sel.tsv`](sel.tsv) | 73 | 17 | 6 | 5 | 2 | 8 | 10 | 121 |
| [`corpus.tsv`](corpus.tsv) | 0 | 0 | 2 | 0 | 0 | 0 | 46 | 48 |
| Total | 2166 | 408 | 270 | 115 | 14 | 359 | 486 | 3818 |

`corpus.tsv` covers the source files that no section table names: bibliographies, layout
files, main files that hold only a title, an abstract and the list of included files,
inventories of earlier reports, verification records, and two tables comparing superseded
bounds. With it, every `.tex` file of every report has at least one row.

209 of the 209 reports appear in at least one table with a disposition other than
`other-unit`.
