# PA194AX11Q6 — a new 194-state consistency-machine composition

This release supplies the requested **materially different 194-state fallback**.
It does **not** claim a machine below 194 states or a lower bound of 194.

Start with `report/pa194ax11q6.pdf`. Its complete LaTeX source and included
fragments are in the same directory. The authoritative literal machine is
`candidate/machine/machine.tm`; the PDF prints all 388 actions.

## Exact claim and convention

The machine uses one two-way infinite tape, alphabet {0,1}, blank 0,
working states 0 through 193, initial state 0, initial head coordinate 0,
and a separate terminal halt label 194. Every step writes one bit and moves
left or right. The halt label is not counted among the 194 working states.

The written mathematical construction, using the retained PA-calculus
calibration, establishes the PA-provable equivalence

    Halt_blank(PA194AX11Q6) <-> there exists a PA proof of 0=1.

Consequently PA proves that its nonhalting is equivalent to Con(PA).
This is an ordinary mathematical PA argument, with executable construction,
source, and physical certificates. It is not a newly compiled end-to-end
Lean/Rocq theorem or a completed machine-specific iPRA endpoint.

Dense machine SHA-256:
`9933fe380b5242981255a0b75da6b305fc88df7031e753411a51efaf7dbe0dab`

Native machine SHA-256:
`3b0a6a7af5bc9ef9b96fab2e810b06f2b219d2c6a703d9bc4862764688372546`

The native label map starts at 74 and halts at 254. The explicit bijection
is `candidate/machine/labels.json`.

## What changes

AX11Q6 combines the inherited AX11 fallthrough protocol, radix-six
constructors, the Q premise exchange, and no-push MP, retaining the original
sum-based Shift guard. AX stores nine axiom entries, the generalized cached
formula, and the saved top; it consumes a fourth operand. It has
135 fixed controls + 67 AX readers - 8 jointly checked folds = 194 states.

This is a new verified composition of attributed ingredients. It changes
the recurring command interface and formula arithmetic. Exact full-tuple
comparison found no equivalent graph among all 82 historical 194-state
classes recognized in the pinned corpus, even allowing all spanning roots,
state renaming, reflection, bit complementation, and ignored final halt
write/move effects. Bit complementation here is a stronger structural test,
not a semantic equivalence preserving a zero blank.

## Contents

- `report/`: compiled PDF, complete TeX report, all 72 delivery comparisons,
  all 82 historical 194-state classes, and the complete new transition table.
- `candidate/`: exact dense/native/raw machines; builder; frozen inputs;
  source binding and splice; grammar/emitter audit; all-store command proof;
  finite premise-exchange certificate; construction and independent literal
  verification code and receipts; retained calibration sources and licenses.
- `comparison/`: pinned repository census, per-packet and per-class ledgers,
  all frontier tables, 193-state rejection certificates, strong novelty
  comparator, and an offline replay requiring no Git or network.
- `research/`: six unsuccessful cyclic-merger searches, exact inputs and
  contexts, C++ sources, logs, portable replay, and a rejected runtime/even
  startup diagnostic. These searches have limited stated scopes.
- `review/`: independent mathematical and source review receipts, plus
  pinned ZFC/ConciseIPRA transfer sources.
- `SHA256SUMS` and `verify_release.py`: release integrity checks.

## Verification already performed

The construction checker passed all 4,901 branch-sensitive outcomes over
arbitrary natural register values and arbitrary permitted spare tails.
It performed 1,571,333 symbolic operations. The independent checker derived
its four list lemmas from literal table rows, used no arithmetic-box oracle,
and passed all 4,901 outcomes in 1,149,402 symbolic operations. Every duration
is strictly positive. Complete blank initialization takes exactly 58,320
literal transitions; the entire finite-support tape is checked.

All 52 physical historical 193-state classes were freshly replayed from
every possible existing blank initial state: 10,036 starts, 106 halts,
9,930 certified outward rays, zero unresolved cases, maximum 117 steps to
certificate. The separate coefficient-three class is rejected by its
inherited logical collision/refutation. The 73,393 figure for that refutation
counts proof lines, not TM steps; its logical replay is attributed, not
claimed as a fresh run here.

The comparison covers 72 delivered packets, 638 recognized spanning action
graph classes, and all 82 historical 194-state classes. It distinguishes
reported constructions from supplementary, research, and rejected tables.
It does not claim all 82 are established consistency machines or that every
historical proof was independently rerun.

## Reproduction

Use Python 3.10 or later, standard library only, without `-O`:

```bash
python3 -B verify_release.py
python3 -B candidate/reproduce.py
python3 -B comparison/replay_audit.py
```

The candidate command builds in a fresh temporary directory and compares
the exact table bytes. It includes both universal physical verification
passes. They are substantially slower than the finite audits. `--quick`
omits those two long passes and is only a structural/source/command smoke
check. Full component checks were run for this release; the packaged quick
wrapper was also tested.

Optional search replay requires g++ with C++17; see `research/README.md`.
The frozen unsuccessful searches do not prove general impossibility.

To rebuild the PDF in a normal TeX Live installation:

```bash
cd report
pdflatex -interaction=nonstopmode -halt-on-error pa194ax11q6.tex
pdflatex -interaction=nonstopmode -halt-on-error pa194ax11q6.tex
```

Run a third pass if TeX still requests one for references or table widths.

## Provenance and proof boundary

Repository: https://github.com/VladimirReshetnikov/ProveIt
Snapshot: `4be5c6e3a10292a7466f5d3687e3b39615ff049b`.

Per-file hashes and paths are in `candidate/PROVENANCE.json`; the current
72-packet ledger includes clickable pinned URLs. The PA calibration sources
are retained under `candidate/proof/references/`. The report identifies the
sensitive translation lemmas, including variable-label recoding, unused
residues, restricted implication, zero aliases, and arbitrary-store proof
compilation. ZFC and ConciseIPRA contribute reduction/proof techniques,
not an unproved replacement of PA consistency by a weaker theory.

Upstream licenses and attribution remain with the copied code. This release
introduces the AX11Q6 composition and binding, its written specialization,
the current comparison and rejection replay, and the stated searches.
