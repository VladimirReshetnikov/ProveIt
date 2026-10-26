# Author receipt: actual machine evolution of one Wang strip row

Date: 2026-10-26 UTC. Author: `controller_certificate`, at root's assignment.
Status: frozen; complete new main/check source self-read and fresh bounded
Lean compilation PASS. This is an author receipt, not an independent review.
Only the two new Lean files and this receipt were authored; no existing
frozen source, maintained equation or shared status file was modified.

All Lean source paths below are relative to `Lean/DiophantineConsistency/`.

| File | Lines | SHA256 |
| --- | --- | --- |
| `WangTiles942RowStep.lean` | 205 | `f4b6f60e4dece143de6d45120c8aa8ae84691d50b1b888e6e0dcb0226f17f84b` |
| `WangTiles942RowStepChecks.lean` | 86 | `29cd6e8dc012c9d0d65fc9f18d2b58fcea3de8fc996d38b4499c68bf74b65fe9` |
| Direct import `WangTiles942HeadBounds.lean` | — | `bed402c366871656a605ebef749451631c88b34ce57118fa6bea583fce700754` |
| Direct import `WangTiles942Signals.lean` | — | `c678e98715e3ef8fa32f179275ba299f3d49256176510821c17056686ba76650` |
| `WangMachineAction.lean` | — | `1776d84d82ae32ec58287779e639ce163bf0e10dec24056effc3aa4c2f1d3bd5` |
| `WangMachineStep.lean` | — | `479ef25344a09804f3eeb6bd980e947941af55965ac48291349f90de14c3f100` |
| `WangTiles942OperatingRow.lean` | — | `f92a15534d5bfdfedb124aef9dac8cc2660b4eacd78562be25066ce66c02e443` |
| `WangTiles942RowEncoding.lean` | — | `d9c24628856b55b6e91b843208539982810d84fbb6f2b5882382b61f4a3cb9df` |

Complemented authored HeadBounds, MachineAction and MachineStep. Circuit
authored Signals and its InputLanguage dependency. Root authored
OperatingRow and RowEncoding. This author previously authored ResetRows,
used inside OperatingRow to derive absence of finishes. The complete
listed dependency sources, InputLanguage and MachineEncoding were read
before execution. Complete new main and checks were each read before
their first execution; all imported sources and objects were already
frozen.

The public theorem has the requested argument order:

```lean
row_step hA hH hTime hs hrow q hq
```

Here `hA` is membership in the actual 942-tile language at all plane
positions; `hH` is actual horizontal matching
`West(T(x+1,t))=East(T(x,t))`; `hTime` is actual temporal matching
`North(T(x,t+1))=South(T(x,t))`; `hs` is the derived persistent strip;
`hrow` encodes `cfg` in that strip at time `t`; and `hq` says the actual
configuration state is `some q`.

The conclusion is the same row-encoding predicate, on the same plane and
same interval, at `t+1` for `DecimalMachine215.machine.step cfg`. No
desired successor row, absence of finishes, clean row, head transition,
machine run, or halting equivalence is supplied as a premise. The next
machine state need not be live: target215 remains a valid successor.

The proof retains three separate cases at every interior coordinate:

- `head_south` uses the exact indexed operating transition and actual
  action binding to identify the written Boolean output at the old head.
- `receiver_south` handles the moved head. The move is exactly one cell
  left or right, so the receiving cell is distinct from the old head and
  has its original plain tape bit. Horizontal matching and the exact
  directional receiver lemma force the actual target-bearing tuple.
  `transition_headColor` identifies its target with the machine's optional
  next state, including halt215 and head colors432/433.
- `far_pass` handles positions distinct from both old and moved heads.
  The two edge-zero lemmas check every possible neighboring location.
  At a wall, its facing edge is at most2 or4, while nonzero receiving
  rails are at least6. At an interior plain neighbor, the actual left
  and right rail sets cannot match a spurious receive/receive signal.
  At an old-head neighbor, a signal toward the cell would make it the
  moved head, contrary to this case; the actual inactive transition edge
  is therefore zero. The independently derived `no_south438` theorem
  then removes the finish alternative, forcing the complete pass tuple.

`south_step` identifies these three tile outputs with the complete
machine color-step formula. The actual direction and the original
destination bit are retained throughout. `row_step` adds the independently
proved `next_head_inside` bound and transfers south colors to the next
row's north colors through actual time matching. The exterior tape is
never read as an unproved row encoding; head containment guarantees every
needed destination cell lies inside the strip.

Focused checks expose the full public signature with no extra cleanliness
premise; prove that entry into halt gives north432 plus the old destination
bit at the moved head; specialize the theorem to the exact signed marked
plane; and derive its second encoded row from the already proved clock1
initialization. The last check supplies neither the initial nor the
successor encoding as a new assumption.

Fresh sequential commands with Lean `v4.32.0`:

```sh
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942RowStep.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942RowStep.lean
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942RowStepChecks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942RowStepChecks.lean
```

Both files passed their first execution without edits. Main diagnostics
are empty, SHA256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The checks log SHA256 is
`6e3f356b31b8c58bc4e3f4c077b0bd23ea7a83e2912ecdd05285a6946d985c86`.
All ten printed axiom reports use only `propext`, `Classical.choice` and
`Quot.sound`. No custom or native-evaluation axiom occurs. Existing
prerequisite objects were reused; this is not a fresh dependency-closure
compilation claim.

Final authored object SHA256s:

- main: `3819b3e23f4b4ef37685caafe3db6c216eaaf46c746e4f2ac89724bc6888effb`;
- checks: `2c1c4038674432ec02e75280e3feaec58ff8cb38a35dad560f10651cdaa38d9d`.

Scope: the packet proves the actual local machine step for an already
encoded live row of the derived strip. Iterating it to obtain halting
from the marked periodic plane, the reverse arithmetic construction and
the complete Diophantine consistency equivalence remain separate modules.
