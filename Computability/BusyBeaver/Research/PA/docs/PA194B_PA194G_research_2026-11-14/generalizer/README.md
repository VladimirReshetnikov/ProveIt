# PA194G: explicit-parameter generalization, 194 states

This folder is a portable construction of a materially different binary,
blank-start, 194-working-state Turing machine. The intended ordinary
arithmetical theorem is

    PA proves: not Halt_blank(PA194G) iff Con(PA).

The complete ordinary mathematical proof is `proof.tex`. It composes a new
all-store command compiler and checked literal implementation with the
retained PA calibration, provided in `references/`. No new end-to-end
Lean/Rocq formalization or iPRA endpoint is claimed.

## Literal machine

`machine.tm` has 388 rows, one for each working state and read symbol.
A row is `state read write L_or_R successor`. Working states are 0 through
193; start is 0; halt label is 194. There are no outgoing halt rows.
Every tape cell is initially zero, and the head starts at coordinate zero.
All transitions move left or right. The halt label is not a working state.

Dense table SHA-256:

    28bd991a84200351f36c98afac369ab5a555eb8793821ad35555f0aa4a0fdeeb

`machine.native.tm` uses the original internal labels; `labels.json` gives
the dense renaming. `raw.native.tm` is the pre-fold construction.

## Material design change

The saved AX generalization is `U(c,h)`, where `c` is the explicit first AX
operand and `h` is the raw incoming cached theorem. The prior command used
`U(d,h)`, with the incoming numerical offset `d`. This is a change to the
command's mathematical interface. For example, with `d=h=0` and `c=1`,
the old saved head is `U(0,0)=2`, whereas the new head is `U(1,0)=10`.
Both are sound generalizations; the different parameter source enables

a shorter generalization compiler:

    Gen_i = Push; Shift; AX_{i,0,0}; Shift^10.

The old offset-setting command is absent. The construction retains the
known Q universal-distribution premise exchange, successful MP without a
dummy push, and the original sum test `t+h=1`. In particular its Pop is
total, even when the current theorem code is one. The refutation compiler
uses an explicit final Shift to detect a returned contradiction.

The accompanying independent command review checks every selector,
generalizer, framed MP word, and all-store detector, including zero-stack
aliases. Structural comparison found no equivalent graph among all 82
prior 194-state classes, allowing arbitrary state renaming, spanning-root
change, reflection, symbol exchange, and ignored effects on terminal
edges. This is a new checked realization of the explicit-operand command
protocol; arbitrary-label theorem generalization itself is established
logic, and is not claimed as a new rule.

## Offline verification

Python 3 and its standard library are sufficient. Do not use `python -O`.
No external repository, downloaded dependency, compiler search, or network
access is needed.

    python3 -B build.py
    python3 -B check_commands.py
    python3 -B independent/check.py . --output independent/replay

The first command checks exact source graph equivalence under association,
the 19-site no-push splice, the seven compatible contextual folds, all
4,755 symbolic physical outcomes, and exact whole-tape initialization.
It writes its receipt to a fresh temporary directory and prints the receipt
content. Use `--output DIRECTORY` to choose the receipt destination.
`--quick` omits its full symbolic physical pass, so it is not a substitute
for the full command above.

The second command checks the full AX emitter over a free term algebra
and the command identities over symbolic stores. It writes
`emitter_and_words_receipt.json` in this folder.

The third uses a separate literal-tape engine. It rederives four induction
lemmas from the actual tape transition rows, independently resolves the
source in two ways, and checks every arbitrary-register outcome. This
last command is deliberately more expensive; it can take several minutes.
Its checks concern arbitrary natural register values, arbitrary nonempty
finite lists of spare blocks, and arbitrary extra nonnegative header gap,
not merely a bounded range of test inputs.

## Evidence and scope

The frozen construction receipt is `verification/construction.json`.
There are 134 fixed controls plus 67 AX readers, with seven compatible
simultaneous folds, giving 194 working states. All 28 local fold cases
pass. The construction symbolic check uses 1,477,258 symbolic steps,
maximum 470 per source outcome. Exact blank startup takes 58,154 physical
transitions to the dispatcher at source site 25, head -2, with logical
registers `(2,0,...,0)` and 26 spare blocks of value one.

The independent literal-tape PASS receipt is under
`independent/results/generalizer_candidate/receipt.json`; its 4,755 checks
used 1,078,742 symbolic steps (maximum 379), with all four induction lemmas
rederived from the rows; its command proof review is
`independent/command_review.md`. `PROVENANCE.json` records the supplied
engines, frozen source inputs, logical calibration dependencies, and
upstream commit. Original license notices are retained in `licenses/`.

The exact table is unconditional finite data. Its consistency equivalence
has an ordinary mathematical proof with executable certificates and
explicit inherited logical calibration. It is not justified by observing
that the machine runs for a large finite number of steps.
