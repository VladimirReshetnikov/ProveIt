# Final bounded check: a five-zero address layout

**Outcome: no accepted reduction. This is not a global impossibility result.**

The baseline 196-state machine has 20 source addresses containing six consecutive
zeros. We inspected the 56 initially allowed physical reader rotations. Exactly
three single rotations both preserved the resolved source CFG and reduced the
number of offending addresses:

| Rotation `(parent, child, side)` | Remaining six-zero addresses |
|---|---:|
| `(90,105,0)` | 15 |
| `(100,174,0)` | 19 |
| `(1342,1320,0)` | 19 |

This filter checked CFG equality, not full symbolic machine correctness. None
of the initially available, individually CFG-preserving moves removes source
ordinal 0's six-zero run.

A two-step root reassociation illustrates why this observation is not a proof
of a structural minimum:

1. Rotate `(84,53,0)`. The only resolved CFG difference is at source3811, whose
   jump target changes from0 to11.
2. Rotate `(53,310,1)`. The complete original CFG is restored. The table still
   has196 working controls, and source0's address is now `00000`.

There are still19 other addresses with a six-zero run. More immediately, the
second layout fails the symbolic contract at source11, the zero branch of CD2
(physical register0), after16 successful contracts. The changed root layout
enters raw69 with previous bit0 instead of1. Row69/0 goes left to213, whose
new read0 branch enters92; the old read1 branch entered90. This selects a
different decoded subtree.

The diagnostic table is `shortscanner_rootrotation196.json`. It is a rejected
candidate, not a verified construction. A failed source contract does not by
itself prove that the candidate's blank-run consistency equivalence is false.

Only the initial56 moves and this particular two-step composition were checked.
No long beam search was started. A five-zero address bound would still require
complete symbolic contracts and an exact blank-start proof before deleting a
scanner state. The structured receipt is `maxzero5_note.json`.
