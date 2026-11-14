# PA194C: a cached-head 194-state machine for Con(PA)

This package supplies the requested materially different 194-state fallback.
No machine below 194 states was established by the reported searches.

The ordinary mathematical result is

```text
PA proves: Nonhalting(PA194C, blank tape) iff Con(PA).
```

The construction combines the accepted PA194 axiom decoder with the existing
195C cached-head Shift/MP controller. The new composition changes six native
transition rows and implements 3,649 primitive source instructions with 4,749
branch outcomes. It is distinct from every recognized 194-state control graph
in the pinned corpus, including the rejected scanner table and global tape
reflections. The cached protocol and decoder folds are credited to their
supplied sources; their verified composition at 194 states is the contribution.

Read **report/pa194c_conpa.pdf** for the comparison, construction, command
compiler, consistency proof, complete transition table, all-archive ledger,
search limitations, and further research questions. The LaTeX and all its
included files are in the same directory.

## Literal machine

`machine/pa194C.tm` has working labels 0 through 193, start 0, and separate
terminal halt label 194. It starts with head at cell 0 on an all-zero, two-way
infinite binary tape. Every row writes a bit and moves exactly one cell L or R.
There are 388 transition rows and no rows for halt. A line is

```text
current_state read_bit write_bit direction next_state
```

Dense table SHA-256:

```text
d759313c03b515293fe06b12769fa1771d3829a2bad89febaa9b4391990f3a4b
```

The native table uses start 74 and halt 254. Its hash is

```text
b35d80b01ce9c2e95c8b29222881f40928247cdeffac322e4643f4f6694cd33c
```

The explicit bijection in `machine/pa194C.labels.json` identifies the two
tables. The complete count is `134 fixed + 67 raw readers - 7 folds = 194`.

## Completed checks

| Check | Result |
|---|---:|
| Working states / transition rows | 194 / 388 |
| Source sites / primitive outcomes | 3,649 / 4,749 |
| Construction checker symbolic steps | 1,507,397 |
| Independent checker symbolic steps | 1,096,302 |
| Independent maximum per outcome | 403 |
| Minimum positive-duration constant | 3 |
| Generic list lemmas rederived from literal rows | 4 |
| Exact whole-tape blank startup | 57,922 transitions |
| Local simultaneous-fold cases | 28 |

The independent checker uses no arithmetic-box oracle. Its contracts quantify
over nine independent arbitrary natural register values, both decrement
outcomes, an arbitrary nonempty finite list of natural spare values, and the
affine header-distance parameter. The startup check compares the entire tape.
The generated instruction map equals the published 195C instruction file,
whose SHA-256 is `0afee1346c0931b3b91fea70571b01fd665a802ab9327409e4030f673412f5e3`.

This is an ordinary mathematical proof supported by executable certificates.
There is **no new end-to-end Lean or Rocq endpoint** for the PA biconditional.
The reference Lean files document inherited components; this is not a
standalone Lean project. The distinction and remaining obligations are
explained in the report.

## Reproduce, without network access

Python 3.10+ and its standard library suffice. From this package root:

```sh
python3 -B verify_release.py
python3 -B construction/build194C.py
python3 -B verification/independent/check194C.py
python3 -B comparison/check_all194_novelty.py \
  --census comparison/census.json \
  --tables comparison/prior194 \
  --candidate machine/pa194C.native.tm
```

Do not use `python -O` or set `PYTHONOPTIMIZE`: assertions perform certificate
checks. The builder reconstructs the new table and the exact published 195C
parent. The independent checker imports neither the builder nor its oracle.
It resolves source edges independently and rederives its list lemmas from the
literal table. These scripts regenerate evidence; check the shipped manifest
before editing or regenerating files.

To rebuild the PDF in a standard TeX Live installation:

```sh
python3 report/build_report.py
```

Equivalently run `pdflatex -interaction=nonstopmode -halt-on-error
pa194c_conpa.tex` twice from `report/`, with an additional pass if requested.
The helper also handles an installation whose prebuilt pdfLaTeX format or
font-map cache is absent.

## Corpus and provenance

The comparison is pinned to ProveIt commit
`768c2be1a8e4d2fcf8aa3443c7b0f084d145734c`.
All 36 incoming ZIPs and 14 direct PA `.tm` files were read. The recursive
numeric-table census recognizes 2,519 occurrences, 606 byte forms, and 437
root-free control graphs. It includes rejected and experimental machines.
The parser covers complete numeric binary `.tm`/`.txt` tables with one halt
target; arbitrary tables embedded solely in source code or JSON are outside
that parser. Two disconnected synthetic controls are excluded from graph
classification. The reports and construction families are compared separately.

The four existing 194-state graphs are PA194 (67 readers minus seven folds),
PA194_AD, the later PA194 allocation (68 readers minus eight folds), and a
rejected seven-zero scanner quotient. The new graph differs from all four
and all their global reflections. All seven old literal forms are included, allowing
the novelty check to run offline. `comparison/census.json` contains the full
member-level inventory; `archive_ledger.csv` and `.json` cover all 36 packets.

A final freshness check incorporated the later PA194 eight-fold packet and
PA195DC packet, with separate targeted searches from the new grammar.

Primary source packets are `pa194_conpa_2026-11-13.zip` and
`PA195_ConPA_research_2026-11-14.zip` under `docs/incoming` at that revision.
Imported licenses are retained in `construction/licenses/` and
`verification/independent/reference/`. The numerical calculus, cached-head
protocol, symbolic engine, and original decoder folds remain credited to
their authors. No upstream repository was modified.

## Package map

| Directory | Contents |
|---|---|
| `machine/` | Dense and native final tables, explicit label bijection |
| `report/` | PDF, full LaTeX source, generated table and archive appendices |
| `construction/` | Reproducible builder, frozen grammar/folds/source inputs, evidence |
| `verification/independent/` | Independent literal-tape checker and complete receipts |
| `comparison/` | Current corpus census, archive ledger, all old 194 tables, novelty replay |
| `reference195C/` | Original cached-head controller and command-calculus proofs |
| `mathematics/` | Independent calibration and source/physical transport audits |
| `search/` | Optional bounded search code, inputs, logs, and explicit limitations |

Negative search results are not state-count lower bounds. The report identifies
the remaining mathematical and compiler questions, including the precise
effective-reader target needed for a 193-state construction.
