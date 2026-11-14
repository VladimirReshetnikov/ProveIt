# PA194QH5

This is a new concrete 194-working-state binary, single-tape, blank-start
construction. No machine below 194 states is established by this package.
The ordinary mathematical proof is in `proof/qh5_preservation.tex`, with
the attributed logical calibration retained under `references/`.

The theorem is `PA ⊢ (not Halt(PA194QH5, blank) ↔ Con(PA))`.
It uses the supplied uniform numerical-calculus calibration and proves the
new coefficient-five source and literal implementation binding. There is
no new end-to-end Lean or Rocq theorem.

## Report and research archive

Start with `report/pa194_qh5_report.pdf`. Its editable source is
`report/pa194_qh5_report.tex`, with the current preservation proof included
from `proof/qh5_preservation.tex`. The report prints the complete transition
table, compares all 66 supplied packets, and lists all 77 recognized
194-control table classes with their evidence status.

The three additional reduction investigations are retained with executable
sources, exact inputs, and receipts:

- `research/startup/`: compound repairs of the supplied 193-state runtime;
  no valid blank initialization was found within the stated search bounds.
- `research/cyclic_mergers/`: a bounded cyclic merger search across 41
  supported or supplementary input constructions; no merger was found.
- `research/eager_shift/`: a counterexample to deleting the Shift wrapper,
  and the corrected 197-state auxiliary that preserves its control flow.

These unsuccessful searches are evidence about their specified finite
search spaces, not state-count lower bounds. The scoped source reviews are
retained in `verification/reviews/`.

To compile the report from this directory, use a normal TeX Live installation
with the standard packages named in the source:

```sh
make report
```

Equivalently, run `pdflatex -interaction=nonstopmode -halt-on-error
-output-directory=report report/pa194_qh5_report.tex` twice. Python verification
does not require TeX. `SHA256SUMS` covers the final release files.

## Concrete contribution

Relative to the supplied PA194QH6 native table, the new row is

```text
190 1 1 R 99
```

where the old target was 330. The exact source changes all 61 constructor
multiplier bodies from six increments to five. All 3,409 primitive sites
outside those bodies, and their successors, are matched by an explicit
relocation. The source has 3,714 sites rather than QH6's 3,775.

The machine combines coefficient-five formula constructors, the Q
premise-exchanged quantifier emitter, visible-result no-push MP, and the
cache-only Shift guard. Those component ideas are prior supplied work.
The new contribution is this exact composition and its fresh verification.
Its graph is absent from all 77 current 194-state literal classes, including
auxiliary and rejected tables, even allowing root changes, renaming,
reflection, symbol exchange, and arbitrary terminal-edge effects.

## Machine convention

`machine/machine.tm` has working states 0 through 193, initial state 0,
and separate halt label 194. The head starts at coordinate 0 on a two-way
infinite all-zero tape. Every row is `state read write direction next`,
where symbols are binary and direction is L or R. There are 388 rows.
`machine/machine.native.tm` uses start 74 and halt 254; `labels.json`
gives the dense-to-native bijection.

Dense SHA-256:
`94c85547b3edd0df0a441d45bf22abb52711f2b27cc9e680999232285757dba5`.

Native SHA-256:
`45c649af2600c2cfa8bbb07ce2a674e07945d985af6c9fc8aaa8563df1225c05`.

## Fresh verification

| Quantity | Result |
|---|---:|
| Working states | 194 |
| Allocation | 135 fixed + 67 readers - 8 folds |
| Source sites | 3,714 |
| Arbitrary-register source outcomes | 4,815 |
| Simultaneous local fold cases | 32 |
| Construction symbolic operations | 1,576,144 |
| Independent symbolic operations | 1,150,677 |
| Independent maximum case length | 403 |
| Minimum positive physical-duration constant | 3 |
| Generic list lemmas rederived from literal rows | 4 |
| Exact complete blank startup | 58,088 steps |

The independent checker imports neither the compiler nor the arithmetic-box
oracle. Its contracts quantify over nine arbitrary natural registers, both
decrement outcomes, an arbitrary affine header gap, and an arbitrary finite
nonempty spare list. The startup checks the entire tape and zero exterior.
Finite startup simulation is used to establish the initial frame, not to
infer infinite nonhalting.

`verification/acceptance.json` records all fresh completed checks.
`machine/independent/` contains the complete literal-tape certificates.

## Offline replay

Use Python 3.10 or later, with assertions enabled:

```sh
python3 -B verify.py
```

The full replay may take several minutes. It rebuilds in a temporary
directory, checks the exact source relocation, free-term emitter and command
identities, 61-line K/S/MP premise-exchange certificate, corpus novelty, and
both complete physical engines. It compares the regenerated machine files
and independent receipt with the delivered versions.

```sh
python3 -B verify.py --quick
```

Quick mode skips only the independent literal-tape engine and explicitly
records that scope. No network, external checkout, optimizer, or proof
assistant is needed. Ordinary mathematical calibration remains a named
proof dependency; running these scripts is not a proof-assistant theorem.

## Comparison

The current source is ProveIt commit
`2337ce611a26e308697ccbddb2a1636f989f01c3`. The ledger covers 61 filed
packets and five incoming archives. The fresh recognizer inspected 10,159
source files and recursively followed retained distinct ZIP payloads. It
recognized 1,467 literal/JSON table occurrences, 649 byte forms, 576
root-free fingerprints, and 563 spanning one-halt graphs. The 77
194-control classes include 34 supported packet constructions, seven
supplementary constructions, 25 research auxiliaries, four research seeds,
six rejected tables, and one disconnected diagnostic. These labels
attribute historical evidence; they are not 77 newly proved consistency
theorems.

All 535 official catalogue representatives were structurally rechecked.
The complete census and all 77 frontier tables are in `comparison/`.
Parameterized unmaterialized generators and arbitrary program encodings
fall outside the literal-table recognition scope.

## Attribution

The supplied ProveIt research, James Chang's register-machine development,
Andrew James Wade's work, and the inherited symbolic verification engines
retain their original attribution. Original notices are in
`verification/reference/LICENSE.*`. `PROVENANCE.json` maps the unchanged
dependencies to their repository paths; `INPUT_HASHES.json` pins them.
The original QH6 proof is retained solely as a historical reference in
`references/qh6_preservation_original.tex`; current claims and metrics are
in the QH5 proof and fresh acceptance receipt.
