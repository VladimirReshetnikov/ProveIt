# PA194N6: a different 194-state machine for Con(PA)

**Result:** no verified machine below 194 working states was obtained. This
package supplies the requested fallback, PA194N6: a complete binary,
one-tape, blank-start Turing machine with 194 working states whose
nonhalting is provably equivalent to Con(PA), in the ordinary mathematical
PA-formalizable sense explained in the report.

Start with **[the 19-page report](report/pa194n6_research.pdf)**. Its complete
editable source is [pa194n6_research.tex](report/pa194n6_research.tex), with
the included `.tex` files in `report/` and `mathematics/`. The full 388-row
transition table is both printed in the report and supplied as
[machine/machine.tm](machine/machine.tm).

## Precise claim and proof boundary

For the delivered literal machine M and a fixed ordinary primitive-recursive
PA proof predicate, the report gives an ordinary mathematical proof of

    PA proves: Halt(M, blank) iff there exists a PA proof of 0 = 1.
    PA proves: not Halt(M, blank) iff Con(PA).

The proof retains and attributes the existing numerical-calculus calibration
to PA, then supplies the new composition's command compiler and source/tape
binding. This release does **not** contain a new end-to-end Lean or Rocq
theorem. The executable checks are finite and symbolic implementation
certificates, with their own stated scope; they are not substitutes for the
logical calibration. No assumption of PA consistency is used to establish
the biconditional. Consistency is the further assumption under which actual
nonhalting follows.

PA194N6 combines two previously separate ingredients: coefficient-six
formula constructors from the M6 packet and omission of the successful-MP
dummy-zero push from PA194N. The composition is new within the pinned
corpus; neither ingredient is claimed to be new by itself. The constructor
arithmetic and the recurring successful-MP stack effect distinguish it from
the prior designs. Its graph is absent from all 30 recognized prior
194-state graph classes, even allowing arbitrary state renaming, a
graph-spanning root change, reflection, and global symbol exchange.

## Exact machine identity

| Property | Value |
|---|---|
| Working states | 0 through 193 |
| Initial state | 0 |
| Separate halt label | 194 |
| Tape | Two-way infinite, alphabet {0,1}, initially all zero |
| Head position | 0 initially |
| Transitions | 388; each writes one bit and moves L or R |
| Table columns | current-state, read-symbol, write-symbol, direction, next-state |
| Formula coefficient | 6 |
| Expanded source instructions | 3,776 |
| Primitive source outcomes checked | 4,877 |
| Exact blank startup to the clean source frame | 58,320 transitions |

Dense table SHA-256:

```text
36da42a81d605ccb8b5edae197c7cde311447bd95b9bf1ab771a3e726a41c6f4
```

The native table uses initial label 74, source entry 84, and halt label 254.
`machine/labels.json` maps dense labels to native labels, including halt.
The native table SHA-256 is
`63b6f604ee34ee119eb92ce3125021257204142854dec416c6b955f0560b975a`.

The parent has 135 fixed controls and 67 AX readers. Eight compatible
history-sensitive folds give 135 + 67 - 8 = 194. Compared with folded M6,
the only native-row change is:

```text
state 164, read 1:  write 1, move R, go to 98
             becomes: write 1, move R, go to 114
```

The report proves that this change implements the specified source splice.
The changed row is not executed during the blank startup or any of the
32 local fold verification traces.

## Reproduce the accepted construction

Python 3.10 or later and the standard library suffice. Run from the package
root, with assertions enabled; do not use `-O` or `PYTHONOPTIMIZE`.

```sh
python3 -B construction/build.py --output generated
python3 -B verification/check.py generated
python3 -B verification/review_structure.py
python3 -B comparison/check_current_novelty.py generated/machine.tm
```

The builder recreates the literal tables, source, folds, and construction
certificate. The independent verifier derives four register-list lemmas
from literal transitions, resolves the source in two separate ways, checks
all 4,877 primitive outcomes, and verifies the complete blank initialization.
The third command separately audits the source splice, folds, startup, and
dense/native relabeling against the frozen parent. The last checks novelty
against the bundled census. These commands need no repository checkout or
network connection. They were run successfully for the delivered machine.

The two complete symbolic runs recorded 1,531,094 and 1,115,525 verifier
operations respectively. Those counts describe certificate execution,
not the running time of the TM's proof search. Recorded receipts and full
independent contracts are under `machine/` and `machine/independent/`.

## Comparison scope

The repository snapshot is
`ffbaf45cadbbc98f5dfd0b473cc8d25c9c21fb9b`:

- [PA research](https://github.com/VladimirReshetnikov/ProveIt/tree/ffbaf45cadbbc98f5dfd0b473cc8d25c9c21fb9b/Computability/BusyBeaver/Research/PA)
- [Incoming research](https://github.com/VladimirReshetnikov/ProveIt/tree/ffbaf45cadbbc98f5dfd0b473cc8d25c9c21fb9b/docs/incoming)

The comparison covers 47 principal research packets: 44 placed packets and
three incoming archives. Its recursive numeric-table census found 3,951
table occurrences, 669 byte forms, and 478 action-graph classes with a
spanning root. At 194 states there are 283 occurrences, 54 byte forms, and
30 classes. The 30-class ledger distinguishes 17 classes with supplied
ordinary PA arguments and independent physical evidence, nine auxiliary
classes, and four rejected classes. This is an evidence classification,
not a fresh reproof of every prior claim.

The automatic scanner recognizes complete five-column numeric binary L/R
tables in `.tm`, `.txt`, `.tsv`, and `.csv` files and recursively visits ZIP
payloads. Arbitrary JSON, source-only definitions, and prose are outside
that recognizer; the narrative packet ledger covers reported contributions.
Two disconnected synthetic fixtures with six and nine controls are excluded
from the spanning-root count. The full census records paths and hashes.

The comparison also finds PA194X and PA194CSZ byte-identical and separately
reproduces three rejected comparator-return variants halting after 1,361
blank-start transitions. See `comparison/` and report Sections 2 and 7.

## Searches below 194

`research/` contains the new grammar-reparsing, mixed-integer, and local
physical reduction experiments, including sources, frozen inputs, receipts,
and unsuccessful results. The searches did not establish a smaller
correct machine. Their failure is not a lower bound on arbitrary machines.
See [research/README.md](research/README.md) for commands and exact scopes.

The local screens can be replayed with a C++17 compiler:

```sh
cd research
python3 replay_physical.py
```

Only the optional mixed-integer grammar experiment needs NumPy and SciPy.
The grammar time limits and proposal counts are recorded as experimental
facts; proposal slots can repeat grammars or be no-ops.

## Rebuild the report

From the package root, with a standard TeX Live installation and the
packages named in the main file's preamble:

```sh
cd report
python3 generate_includes.py
pdflatex -interaction=nonstopmode -halt-on-error pa194n6_research.tex
pdflatex -interaction=nonstopmode -halt-on-error pa194n6_research.tex
```

Run one additional LaTeX pass if requested for table widths or references.
The delivered PDF was rendered and visually inspected. PDF metadata and
LaTeX version differences can change PDF bytes without changing its content.

## Package map and provenance

| Path | Contents |
|---|---|
| `report/` | Compiled report, complete main LaTeX source, generated tables, regeneration script |
| `mathematics/` | New generalized command compiler and exact source-splice proofs |
| `machine/` | Literal tables, dense/native bijection, source, folds, receipts, independent contracts |
| `construction/` | Reproducible builder, bundled parent inputs, provenance, inherited notices |
| `verification/` | Separate literal/source verifier and independent structural review |
| `calibration/` | Attributed inherited logical proofs and relevant Lean reference sources |
| `comparison/` | Census, all 47 packet contributions, all 30 prior 194-state classes, novelty check |
| `research/` | Unsuccessful state-reduction experiments and replay commands |
| `licenses/` | Retained upstream notices |
| `RESULTS.json` | Machine-readable release facts and limitations |
| `SHA256SUMS` | Checksums of every other delivered file |

Upstream source identities and hashes are retained in
`construction/PROVENANCE.json`, the census, and inherited source headers.
The parent formula-coding packet is
`Computability/BusyBeaver/Research/PA/docs/pa194_radix_family_2026-11-13`;
the no-push ingredient is `docs/incoming/pa194N_conpa_2026-11-13.zip`.
The report also explains which ideas transfer from the ZFC and ConciseIPRA
projects and why their logical-strength calibrations cannot be substituted
without a separate proof.

To check the delivered bytes on a platform with GNU coreutils:

```sh
sha256sum -c SHA256SUMS
```

Regenerating time-dependent logs or LaTeX intermediates may produce
additional files; the manifest describes the original release.
