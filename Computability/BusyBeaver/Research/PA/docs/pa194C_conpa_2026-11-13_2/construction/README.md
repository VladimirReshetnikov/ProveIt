# PA194C: a materially different 194-state PA consistency machine

`output/pa194C.tm` is the complete binary one-tape table, on a blank two-way
tape, with start state 0, working states 0--193, and halt state 194. It has
388 transitions. Its native counterpart starts at 74 and halts at 254.

This construction combines the prior PA194 axiom decoder and its seven
simultaneous folds with the prior Combined command controller. It changes
the Shift halt condition and the successful modus-ponens store update;
the complete source program has 3,649 sites instead of 3,673. The new
194-state graph is absent from the supplied corpus even modulo state
renaming, start reassignment, reflection, and bit complementation.

The ordinary mathematical result, with the inherited numerical-calculus
calibration and the fresh physical certificates, is

    PA proves: not Halt(PA194C, blank) iff Con(PA).

This archive does not claim a new end-to-end Lean or Rocq theorem. The
logical proof, executable certificates, and existing formal endpoints have
different scopes; see `proof_notes.txt` and `PROVENANCE.json`.

## Reproduce

Python 3 and its standard library suffice; do not use `-O`.

```sh
python3 build194c.py
python3 verify194c_independent.py
python3 command_audit/check_composite_commands.py
```

The builder checks all 28 simultaneous local-fold cases and all 4,749
arbitrary-register symbolic source outcomes. The independent checker uses
no arithmetic-block oracle: it rederives four generic list-sweep lemmas
from the literal table and checks all source outcomes for arbitrary natural
register values, affine tape gaps, and arbitrary finite nonempty spare
lists. The exact startup is 57,922 tape steps, comparing the entire final
tape, head position, and state against the clean source frame.

The independent receipt records 1,096,302 symbolic transitions, at most 403
per source outcome, with strictly positive duration in every case. These
are proof-case sizes, not numerical bounds on the full machine's execution.

`construction/` and `reference/` contain the credited inherited finite
compiler and symbolic-engine sources. `proof_sources/` retains the supplied
logical arguments needed for the calibration. New construction and
verification code is in the two top-level Python scripts. `output/` and
`independent/` contain the freshly generated artifacts and receipts.

The input repository revision and archive hashes are in `PROVENANCE.json`.
The inherited ProveIt and James Chang licenses are preserved in
`construction/licenses/`.
