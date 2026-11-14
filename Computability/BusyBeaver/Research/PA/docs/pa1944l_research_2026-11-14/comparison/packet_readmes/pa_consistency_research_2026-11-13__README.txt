# PA-consistency machines: comparison and diagonal-vacuity research

**Outcome: no machine with fewer than 196 working states was obtained.**

The smallest validated table in the comparison remains James Chang's published
196-state machine. This archive supplies a new, shorter PA-calibrated axiom
program and an explicit **199-state** binary blank-tape implementation. It is a
research result and reproducible negative search, not a 195-state construction.

Read `report.pdf` for the comparison, the complete written calibration argument,
and verification limits. The LaTeX source is `report.tex` plus `sections/*.tex`.

## Main files

| Path | Role |
|---|---|
| `report.pdf`, `report.tex`, `sections/` | Report and all TeX source |
| `diagonal199/machine.tm` | New literal binary table: 199 working states, 398 rows |
| `diagonal199/machine.native.tm` | Same table with sparse internal state labels |
| `diagonal199/dense_labels.json` | Exact dense/native bijection, including halt |
| `diagonal199/source.tree.json` | Complete primitive source tree, 3,700 sites |
| `diagonal199/ax_macro_tree.json` | New 191-item axiom macro grammar |
| `diagonal199/folds.json` | Four validated folds from 203 to 199 states |
| `diagonal199/receipt.json` | Counts, source audit, and exact hashes |
| `reference/pa196/` | Small frozen upstream inputs used by the checks |
| `reference/pa209/` | Exact historical 209-state table and license |
| `reference/proveit/` | Nine U208 table presentations and license |
| `verification/` | Portable standard-library Python checkers and receipts |
| `verification/lean/` | New generic engine lemma and dependency sources |
| `verification/search/` | Bounded quotient-search C++ sources, contexts, logs |
| `experiments/` | Validated 197- and 201-state unsuccessful reductions |
| `notes/` | Supporting proof and research notes |
| `SOURCES.md` | Frozen revisions, attribution, and source provenance |
| `SHA256SUMS` | Hashes of the delivered files, excluding itself |

## Machine convention

Each transition line is `state read write direction next_state`. The tape is
two-way infinite and initially all zero. The head starts at any fixed origin in
state **0**. Working states are **0 through 198**. State **199** is the halt label
and has no rows. Each step writes 0 or 1 and moves exactly one cell left (`L`) or
right (`R`). The halt label is excluded from the 199-state count.

The native presentation starts in state 74, uses decoder root 84, and halts at
254. Native labels are identifiers, not a count. The dense table's SHA-256 is:

```
6c29db7f324a0d18ee7dc5bfaa3f9b734011c453586d0bc1b96754a6bab4e52c
```

## Reproduce the finite checks

From this directory, using Python 3.12 (only the standard library is required):

```bash
python3 verification/check.py --experiments
python3 verification/check_emitter.py
python3 verification/rebuild.py --verify-stages
python3 verification/compare_proveit.py
```

The first command checks complete tables, the 42 fixed engine rows, all symbolic
primitive contracts, exact startup, and dense/native conjugacy. Expected core
results are:

| Machine | Working states | Source sites | Symbolic cases | Startup transitions |
|---|---:|---:|---:|---:|
| Published PA196 | 196 | 3,812 | 4,959 | 58,154 |
| New diagonal-vacuity implementation | 199 | 3,700 | 4,815 | 58,154 |
| Original calculus with negation peephole | 197 | 3,596 | 4,671 | 58,154 |
| Original calculus repacked | 201 | 3,812 | 4,959 | 58,154 |

The emitter check compares constructor trees in a free algebra: the top is the
new gate, all nine saved stack expressions are unchanged, and the macro word
shrinks from 201 to 191 items. The rebuild check audits the macro and outer
ordinal control-flow graphs, compiles the exact initial 203-state table, applies
the four recorded folds, and compares the final table literally. The optional
`--verify-stages` also replays all contracts and startup after each fold.

The U208 comparison retains written bits and directions and compares rooted,
read-symbol-labelled graphs. The nine presentations fall into **two** classes.
The generated comparison JSON contains canonical hashes and full renaming maps.

`python3 diagonal199/verify.py` is an additional self-contained replay focused
on the new table. It uses the same symbolic runtime method and is not an
independent proof kernel.

## Reproduce the Lean engine check

Install Lean **4.35.0**, put `lean` on `PATH`, and run:

```bash
bash verification/lean/check.sh
```

This builds `Zip`, `Runtime`, `Reference230`, and `NativeMinimal`. The new theorem
is `M6.NativeMinimal.boxLemmas`. It reduces the generic agreement hypothesis to
41 rows, with row `(198,0) = (1,L,40)` checked separately. Its printed axioms are
`propext`, `Classical.choice`, and `Quot.sound`. The archive excludes Lean
executables and generated `.olean` files.

## What is proved, checked, or still unformalized

- The original repository explicitly supplies the internal implication from
  nonhalting to `Con(PA)`, plus external nonhalting and PA independence results.
- The report gives a **written syntactic proof construction** of the reverse
  PA-internal implication, using uniformly generated PA proofs of finite binary
  comprehension. It is a proof-code translation, not a truth predicate.
- The report gives a new diagonal-vacuity calculus and recovers the original
  compiler's reverse-rewriting, neighborhood-equality, and witness interfaces.
- The exact new table, source CFG, emitter, startup, and uniform primitive
  contracts pass the supplied executable checks.
- The new generic engine lemma is kernel checked in Lean. A complete new Lean
  development of the diagonal calculus, its two arithmetic translators, and all
  4,815 new table coverage cases **is not included or claimed**.
- No finite nonhalting simulation proves the desired independence statement;
  the calibration argument is essential.

## Bounded searches

See `verification/search/README.md` for compiling and rerunning the local search.
The two largest syntheses tested 5,650,476,975 parameter choices for PA196 and
6,176,511,792 for the 199-state machine. Both found no hit in that family. These
are bounded windows and bounded detours with protected interfaces; they are
**not global lower bounds**, and the counts need not count distinct machines.

## Build the PDF

With a standard TeX Live installation:

```bash
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

All required TeX inputs are included; no network access is needed for the build.

## Attribution

Upstream code and tables retain their accompanying licenses. Frozen revisions
and exact source links appear in `SOURCES.md` and the report. New report text and
scripts are supplied with the MIT license in the archive root; that license
does not replace any upstream notice.
