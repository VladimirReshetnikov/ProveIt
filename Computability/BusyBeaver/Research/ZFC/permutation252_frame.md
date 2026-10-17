# Frame interface for the register-permutation252 candidate

The new candidate retains all original logical and theory instructions. It folds
old state 5 into 64, then retargets eligible physical-register selectors by
`[0,3,4,5,8,1,6,2,7]`. The frozen old-label table has 252 working states and 504
actions; SHA-256 is
`939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713`.
This is separate from the older uncalibrated `Table252` grammar experiment.

An independent literal interpreter reproduced the complete blank run to old
dispatch 96 after 82,552 moves: absolute head 2, marker 1, header 42, empty PC,
nine zero primary registers, and 65 spare blocks. Only spare 8 has value 1.
All 77 one positions agree with the C++ census after its exact seven-cell head
translation. The census skips nine common first-write steps; step count and
head translation are different quantities. Durable reproduction and source
hashes are in `results/breakthrough-permutation-census-independent-audit.json`.

`Permutation252Frame.lean` passed the pinned Lean 4.32.0 compiler in 0.688
seconds. Its 17 theorem axiom reports and four callers passed in 0.638 seconds,
using only `propext` and `Quot.sound`. The last caller consumes the exact checked
82,552-step binary bootstrap and proves the actual zero-root dispatch frame.
Source hashes, audit source and output are preserved in
`results/permutation252-frame-verification.json`. The module defines
the exact new logical-to-physical map
`[6,2,0,4,3,7,8,5,1]` and its inverse physical order
`[2,8,1,4,3,7,0,5,6]`. Finite inverse/composition checks and unrestricted-value
list identities relate logical register reads and updates to physical blocks,
including an arbitrary spare suffix. Its generic `DispatchFrame` specifies the
entire zero-exterior tape, integer head and dispatch state, with
`40 ≤ PC.length + gap` and a zero logical register tail. An independent bootstrap
theorem can supply its zero-root constructor without assuming execution from
the frame definition.

The zero tail belongs to the abstract logical register vector, as in
`L2.enc`. The concrete physical spare suffix is a separate list and may contain
nonzero values. The complete site checks establish that every logical
register operation selects an index below nine; the frame map then implements
those nine registers and preserves the arbitrary spare suffix. It does not
identify physical spare values with the unused logical tail.

There is no spare capacity or spare-zero obstacle in this interface. The actual
upstream `Box.v` lemmas `box_mark`, `box_inc`, `box_dec0`, and `box_decp` require
only at least nine represented blocks. They permit arbitrary remaining values.
Increment shifts that suffix intact; zero decrement preserves it; positive
decrement appends a new zero block. The quantified `ext` in `Sim.v`'s `Inv` has
no further value or length condition. The current Lean increment and decrement
proofs have the same unrestricted suffix interface. These statements concern
the unchanged register boxes; they do not prove the whole modified interpreter.

The separate `Permutation252Program.lean` first composes the safe
all-zero dirty-root theorem with `Bisim254.prog254_halts_iff` to obtain the
literal `Prog254` program's equivalence with the numerical statement
`Code254.C254 Code254.F`. Its native CP/all-Form-GIC/IR refutation endpoint is
then derived through `NativeTheory254.c254_refutation_iff`. The complete fast
bisimulation certificate has passed the local pinned compiler in 555.41
seconds; see `results/bisim254-optimized-verification.json`. The small Program
module passed the pinned compiler in 0.52 seconds; both theorem axiom reports
and four callers passed in 0.40 seconds. Both closures use `propext`,
`Classical.choice` and `Quot.sound`, even though the numerical theorem does not
compose the native semantic equivalence. Evidence is in
`results/permutation252-program-verification.json`. These register-program
theorems supply no binary simulation by themselves.

The exact canonical table and 82,552-step bootstrap have separately passed
the kernel check. The [complete decoder coverage](site_coverage.md) has now
passed all 8,391 guard cases in eight saved batches and the final structural
composition. A closed audit composes the [instruction and runtime
proofs](permutation252_runtime.md) with this frame and the register-program
endpoint, giving actual blank-machine halting iff numerical, native-theory,
and ZF refutation. Its 23 axiom reports and seven caller controls passed in
0.65 seconds; full evidence is in
`results/sites-permutation252-verification.json`. The [standard-ZFC Choice comparison](choice_calibration254.md)
is also closed externally. [PA internalization](pa_internalization.md) remains
open.

Sources: `lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Box.v:233,248,270,286`,
`Sim.v:81–84,161–165`; Lean `RegisterIncrement253.increment_zip`,
`RegisterDecrement253.positive_decrement`, `DirtyProgram254`, and `Bisim254.prog254_halts_iff`.
