# A 194-state Turing machine calibrated to Con(PA)

The primary result is **a complete binary, one-tape, blank-start Turing
machine with 194 working states** for which the accompanying mathematical
proof establishes

```text
PA proves: Nonhalting(PA194, blank tape) if and only if Con(PA).
```

Open `report/pa194_conpa.pdf` for the 18-page construction, comparison,
proof, complete transition table, and ledger of all 32 incoming archives.
The complete LaTeX source and its included files are beside the PDF.

The mathematical result is supported by two implementations of the
symbolic physical verification, explicit source identity, exact blank
initialization, and the inherited syntactic PA calibration. It is an
ordinary mathematical proof of a PA-provability statement. This release
does **not** claim a newly compiled end-to-end Lean or Rocq theorem.

## The literal machine

`construction/tables/pa194.tm` is the principal dense table. It has working
states 0 through 193, initial state 0, and separate terminal halt label 194.
The head starts at cell zero of an all-zero, two-way infinite tape. The
alphabet is `{0,1}`; every transition writes a bit and moves one cell left
or right. There are 388 rows, with no rows for the halt label. A row is

```text
current_state read_bit write_bit direction next_state
```

The source program is exactly the supplied 195S program: 190 axiom-emitter
macro tokens and 3,673 resolved primitive instruction sites. Reassociation
of its binary decoder supports 67 raw readers and seven simultaneous
history-sensitive folds. The complete count is

```text
134 fixed controls + 67 raw AX readers - 7 folds = 194 working states.
```

The earlier allocation patterns were `134 + 68 - 7 = 195` and
`134 + 67 - 6 = 195`. The saving combines the smaller raw allocation and
the larger compatible fold set. The final construction uses identity
axiom-head parameter permutations and the original 195S register layout.

The primary dense table SHA-256 is

```text
4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f
```

The archive also includes `construction/tables/pa194_AD.tm`, a second
194-state table that exchanges the physical A and D register positions.
It differs in three native transition rows and has a different control
graph even after arbitrary control renaming or left/right reflection.
Its blank initialization is 32 transitions shorter. This is an
initialization comparison, not a claim of a uniform speed improvement.

## Reproduce the construction and checks

Python 3.10 or later and its standard library suffice for all primary
construction and verification commands. From this package's root:

```sh
python3 -B construction/build194.py
python3 -B construction/rotation194.py
python3 -B construction/build194_ad.py
python3 -B verification/independent/check.py
python3 -B verification/independent/compare_pair.py
```

Assertions must remain enabled: do not use Python `-O` or `PYTHONOPTIMIZE`.
The independent command checks both `PA194` and `PA194_AD`; use
`--family PA194` to select only the primary. It writes its replay evidence
to a fresh temporary directory unless `--output PATH` is given. The
primary builder can also write reconstructed tables using `--output PATH`;
the companion uses `--write` to regenerate its delivered table files.
The recorded observed outputs are already included under
`construction/evidence/` and `verification/independent/recorded/`.

| Verified quantity | Primary PA194 | A/D companion |
|---|---:|---:|
| Working controls / transition rows | 194 / 388 | 194 / 388 |
| Unchanged source instruction sites | 3,673 | 3,673 |
| Symbolic source outcomes, each checker | 4,780 | 4,780 |
| Construction checker symbolic steps | 1,479,348 | 1,479,348 |
| Independent checker symbolic steps | 1,078,198 | 1,078,321 |
| Independent maximum per outcome | 397 | 397 |
| Minimum positive-duration constant | 3 | 3 |
| Exact whole-tape blank startup | 58,154 | 58,122 |

These are universal symbolic register contracts, including both decrement
outcomes, rather than bounded tests of register values. The frame domain
uses arbitrary nine natural register values, an arbitrary finite nonempty
spare list, and header distance `48 + n`, for any natural `n`. After source
path `p`, the zero gap is `48 + n - |p|`. The independent implementation
uses no arithmetic-box oracle: it rederives four generic list lemmas from
the actual transition rows before checking every source outcome.

The construction also checks all 28 local two-cell fold cases in the
**final simultaneously folded table**, together with 23 incoming-context
rows. A separate 369-move association certificate connects the endpoint
emitter trees. Complete source-map identity is checked separately, since
word identity alone would not preserve structured jump destinations.

The finite startup runs check the entire tape, including markers, source
bits, all register and spare blocks, and zero exterior. The logical seed
is source site 25, native control 84, head -2, register vector
`[2,0,0,0,0,0,0,0,0]`, and 26 one-valued spare blocks. The nonhalting result
depends on the mathematical consistency calibration, not on extrapolating
these finite runs.

## Package map

| Path | Contents |
|---|---|
| `report/` | PDF, full LaTeX source, transition-table appendix, archive ledger, and inherited calibration references |
| `construction/tables/` | Dense and native 194-state tables, label bijections, raw 201-state table |
| `construction/source/` | Frozen new grammar, folds, complete instruction map and source sites |
| `construction/inputs/` | Exact supplied 195S parent grammar, folds and native table |
| `construction/evidence/` | Observed construction checks, local fold cases and rotation witness |
| `verification/independent/` | Separate literal-tape symbolic checker, source resolvers, complete recorded certificates and pair comparison |
| `comparison/` | Pinned recursive census, all 32 archive contributions, existing 195-state classes and literal tables |
| `search/` | Discovery code, numeric search inputs, actual run logs, frozen winner and bounded negative results |
| `RESULTS.json` | Compact machine-readable release facts and proof scope |
| `SHA256SUMS` | Hashes of all release files other than the hash file itself |

Optional discovery searches use a C++17 compiler. Their negative results
are limited to the stated families and are not lower bounds. Repeating a
time-limited stochastic search is unnecessary for reconstructing and
checking the frozen successful construction.

To rebuild the PDF in a standard TeX Live installation with the packages
listed in the document preamble:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error pa194_conpa.tex
pdflatex -interaction=nonstopmode -halt-on-error pa194_conpa.tex
```

An additional pass may be needed if LaTeX requests it for references.
Before regenerating any evidence, verify release integrity from the package
root with `sha256sum -c SHA256SUMS`. Replaying a builder updates its receipt,
including elapsed time, so regenerated receipts can have different hashes.

## Corpus, provenance and attribution

The comparison is pinned to ProveIt commit
`5ed5a41fa5932433111eea096311364c6087e8e3`, including the requested
[PA research](https://github.com/VladimirReshetnikov/ProveIt/tree/5ed5a41fa5932433111eea096311364c6087e8e3/Computability/BusyBeaver/Research/PA),
[incoming archives](https://github.com/VladimirReshetnikov/ProveIt/tree/5ed5a41fa5932433111eea096311364c6087e8e3/docs/incoming),
[ZFC research](https://github.com/VladimirReshetnikov/ProveIt/tree/5ed5a41fa5932433111eea096311364c6087e8e3/Computability/BusyBeaver/Research/ZFC),
and relevant concise-iPRA sources. The census traverses all 32 top-level
incoming archives, 45 distinct ZIP payloads and 73 archive references.
It recognizes 2,360 numeric complete binary table occurrences, 582 byte
forms and 421 classified control graphs, including experimental and
rejected machines. These are not counts of established consistency
constructions. At 195 states there are three positive manuscript
families and six rejected or diagnostic graph classes. No 194-state
table occurs in this recognized pinned corpus.

The new saving is a reader-tree allocation and compatible quotient of
the existing 195S source. The existing numerical calculus, compiler
interfaces and proof transformations are credited to their supplied
sources. The physical A/D permutation technique was already present
in a 196-state report. Imported licenses and provenance are preserved
in `construction/licenses/`, `construction/PROVENANCE.json`, and the
independent verifier's `reference/` directory. Reference Lean files
document inherited components; this package is not an end-to-end Lean
project.

The report is dated **13 November 2026, Pacific time**. Some supplied
archive filenames use 14 November in UTC. No global optimality claim is
made for the achieved 194-state count.
