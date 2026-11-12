# A closed Q theorem lost by hypothesis-only major elimination

## Exact result

The byte-identical original flat-computation checker accepts the canonical
closed theorem

    Q_y (0=0).

The supplied variant changes only the requirement on an elimination major:
its opened formula must already occur in the retained hypothesis context;
the checker can no longer recursively prove that major. The variant rejects
the same certificate. The formal root invariant below shows that it cannot
prove this Q theorem by any other finite canonical certificate either.

This is a negative result about this exact rule deletion and the existing
Eq/Q/D public formula language. It is not a claim about all possible Eq/D
redesigns, and is not a positive axiomatization breakthrough.

## Three-element certificate

Input instructions are consumed from right to left, after the final goal:

```json
[[[],0,0,0],[[0,0,[0,0]],0,0,0],[[0,0]]]
```

- The final `[[0,0]]` is `Q_y(0=0)`.
- The preceding packet requests elimination of `D_xy(0=0)`.
- The first packet introduces that D formula in case mode with witness zero.
  Its minor goal `0=0` equals its local hypothesis, so it closes by Hyp.
- Returning to DE opens the Q hypothesis, which closes the outer Q goal.

The inspected pinned named producer emitted exactly this certificate.
`named_derivation.json` records its proof tree and emission trace. The
producer is not imported by either checker or the reproduction script.

## Formal derivation

Let `E` be the equation `0=0`, independent of all displayed variables.

1. `E |- E` by Hyp.
2. `|- D_xy E` by DI-case, choosing witness zero and discharging the local
   assumption E. Since E is constant, its zero and successor instances agree.
3. `Q_y E |- Q_y E` by Hyp.
4. `|- Q_y E` by DE applied to steps 2 and 3, with a fresh unused witness.

The derived D theorem in step 2 is the major of step 4. That is precisely
what the restricted checker removes.

## Why adding atomic induction at goals does not repair this example

The experimental variant does not add a direct equation-goal induction
branch. This omission does not weaken the mathematical obstruction.
Starting with a closed Q-root goal and an empty context, equation computation
supply adds only equations. A literal-equation induction rule would conclude
only an equation and, within its branches, add only an equation hypothesis.
DI concludes D, not Q. Numerical equality transport preserves the Q root
of its target and minor. Hyp cannot close a Q goal from equation-only
hypotheses; QE requires a Q hypothesis, and DE requires a D hypothesis.
Thus no finite Q-root derivation can start in that setting. This is an
induction on proof height, independent of which equations direct induction
can establish.

A new Q introduction rule, a verified theorem-supply rule, or exclusion of
Q from public goals changes the system and requires separate accounting.

## Reproduce

Run with Python 3.12 or compatible Python 3:

```sh
python3 reproduce.py
```

The script first verifies the original source hash and the exact isolated
mutation. It then checks seven cases against both programs under ordinary
and optimized Python: 28 process runs. The recorded run passed all 28.

Expected outcomes:

| Case | Original | Hypothesis-major variant |
|---|---|---|
| Closed Q reflexivity | ACCEPT | REJECT |
| Paired constant identity | ACCEPT | ACCEPT |
| Genuine arithmetic supply | ACCEPT | ACCEPT |
| False varying closure `Q_y(y=0)` | REJECT | REJECT |
| Outer Q goal mismatching the supplied Q | REJECT | REJECT |
| Unallocated parameter in the closed goal | REJECT | REJECT |
| Paired major with no proof instructions | REJECT | REJECT |

The controls confirm that the theorem certificate's acceptance does not come
from ignoring the Q goal, accepting an unproved major, or leaking a fresh
parameter. They supplement the formal proof; finite runs alone would not
establish nonderivability of every alternative certificate.

## Provenance

Repository: `VladimirReshetnikov/ProveIt`.
Pinned commit: `0300a290bedee5019c974291850b798378438b2e`.
Archive: `docs/drafts/ipra_flat_computation_2026-11-10.zip`.
Original member: `ipra_flat_computation_2026-11-10/code/checker.py`.
Original SHA-256:
`8ac122714ebb0f3351d6eb9a7bf3b97031e2055436ea83b2e20d5c81b80acf06`.

`provenance.json` contains the source/archive hashes and exact mutation.
`results.json` contains every expected/actual verdict, exit code, stdout,
and stderr. Both checkers are complete standalone Python programs using
only the standard JSON library. The original source retains its license
from the repository, supplied in `LICENSE-ProveIt.txt`.
