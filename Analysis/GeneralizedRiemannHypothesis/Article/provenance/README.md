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
in the history (the first 103 at commit `10802a6b36`, the next 17 at commit `f2f9fd7531`, the next 11 at commit `64f3896557`, the next 11 at commit `fd9a9cb2bd`, the next 42 at commit `f6b5955e13`, the next 10 at commit `7f951e1dfd`, the next 15 at commit `3c4d27a69c` and the last 33 at commit `2f9fb0b144`); the packets are no longer in the working tree.

Labels have the form `<key>:<kind>:<name>`. `<key>` names the section file the result was first
merged into; results moved when the article was regrouped on 27 November 2026 kept their labels,
so a label's prefix need not match the file that now holds it. Each table lists the rows whose
target is in its section file. The
`conflict` rows mostly concern how the reports describe the upstream proof; the article
uses the latest, corrected description.

| Table | `merged` | `duplicate` | `subsumed` | `answered` | `conflict` | `other-unit` | `non-mathematical` | Rows |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| [`src.tsv`](src.tsv) | 59 | 97 | 6 | 0 | 9 | 28 | 55 | 254 |
| [`spn.tsv`](spn.tsv) | 64 | 2 | 4 | 3 | 0 | 6 | 51 | 130 |
| [`ana.tsv`](ana.tsv) | 97 | 21 | 20 | 3 | 1 | 20 | 36 | 198 |
| [`li.tsv`](li.tsv) | 84 | 0 | 3 | 1 | 0 | 10 | 20 | 118 |
| [`lih.tsv`](lih.tsv) | 94 | 11 | 4 | 3 | 0 | 0 | 10 | 122 |
| [`nab.tsv`](nab.tsv) | 70 | 8 | 23 | 4 | 0 | 32 | 25 | 162 |
| [`grp.tsv`](grp.tsv) | 75 | 0 | 1 | 4 | 0 | 14 | 12 | 106 |
| [`hec.tsv`](hec.tsv) | 57 | 11 | 1 | 0 | 0 | 14 | 5 | 88 |
| [`zer.tsv`](zer.tsv) | 46 | 2 | 2 | 1 | 0 | 47 | 55 | 153 |
| [`flu.tsv`](flu.tsv) | 86 | 11 | 8 | 5 | 0 | 0 | 1 | 111 |
| [`fil.tsv`](fil.tsv) | 150 | 38 | 26 | 12 | 0 | 11 | 28 | 265 |
| [`zfg.tsv`](zfg.tsv) | 70 | 14 | 6 | 2 | 0 | 0 | 1 | 93 |
| [`rec.tsv`](rec.tsv) | 107 | 4 | 7 | 2 | 0 | 27 | 46 | 193 |
| [`chz.tsv`](chz.tsv) | 145 | 19 | 11 | 3 | 0 | 0 | 3 | 181 |
| [`cpl.tsv`](cpl.tsv) | 71 | 8 | 16 | 4 | 0 | 0 | 0 | 99 |
| [`eul.tsv`](eul.tsv) | 70 | 28 | 24 | 5 | 0 | 0 | 4 | 131 |
| [`dir.tsv`](dir.tsv) | 43 | 6 | 1 | 0 | 2 | 39 | 76 | 167 |
| [`prd.tsv`](prd.tsv) | 184 | 31 | 11 | 6 | 0 | 0 | 1 | 233 |
| [`cls.tsv`](cls.tsv) | 32 | 7 | 11 | 5 | 0 | 20 | 6 | 81 |
| [`cmf.tsv`](cmf.tsv) | 27 | 1 | 2 | 1 | 0 | 0 | 0 | 31 |
| [`smd.tsv`](smd.tsv) | 120 | 28 | 30 | 10 | 0 | 16 | 13 | 217 |
| [`gpp.tsv`](gpp.tsv) | 75 | 6 | 9 | 8 | 0 | 0 | 6 | 104 |
| [`gpi.tsv`](gpi.tsv) | 37 | 9 | 14 | 5 | 0 | 24 | 7 | 96 |
| [`gra.tsv`](gra.tsv) | 82 | 11 | 3 | 5 | 0 | 15 | 3 | 119 |
| [`grw.tsv`](grw.tsv) | 68 | 4 | 3 | 1 | 0 | 0 | 1 | 77 |
| [`cmp.tsv`](cmp.tsv) | 276 | 57 | 25 | 15 | 0 | 0 | 11 | 384 |
| [`tors.tsv`](tors.tsv) | 63 | 15 | 9 | 8 | 0 | 10 | 4 | 109 |
| [`cost.tsv`](cost.tsv) | 88 | 3 | 7 | 5 | 0 | 10 | 10 | 123 |
| [`lub.tsv`](lub.tsv) | 72 | 12 | 11 | 4 | 0 | 8 | 12 | 119 |
| [`sel.tsv`](sel.tsv) | 73 | 17 | 6 | 5 | 2 | 8 | 10 | 121 |
| [`corpus.tsv`](corpus.tsv) | 0 | 0 | 2 | 0 | 0 | 0 | 46 | 48 |
| Total | 2585 | 481 | 306 | 130 | 14 | 359 | 558 | 4433 |

`corpus.tsv` covers the source files that no section table names: bibliographies, layout
files, main files that hold only a title, an abstract and the list of included files,
inventories of earlier reports, verification records, and two tables comparing superseded
bounds. With it, every `.tex` file of every report has at least one row.

242 of the 242 reports appear in at least one table with a disposition other than
`other-unit`.
