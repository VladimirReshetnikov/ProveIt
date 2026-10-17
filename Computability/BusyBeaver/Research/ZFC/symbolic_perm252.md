The generic symbolic checker for the new 252-state register permutation candidate is
kernel checked in `SymbolicPerm252.lean`, including its verified balanced table
lookup. The earlier direct-lookup PASS is preserved separately in
`results/symbolic-perm252-raw-lookup-verification.json`.
It uses the actual compact 252-state table and the four proved register-file routines. Those routines are conclusions
about literal Core execution, rather than hypotheses passed to the checker.

The segment language follows Mira-Cult's published `SymExec.v` at upstream
`297ab8df7e5de329605c3875b4934643b371a5e3`, attributed to Mira-Cult and Jeff,
with Wade's compiler framework. The public 253-state reduction is attributed to
mira-emmy's PR20 head `0d544f2a2e3c18f12278441a74b7879f31cbe856`. This is a new
Lean proof for the separately frozen permutation candidate; it does not import
or assume the upstream symbolic-execution proof.

`Segment.bit`, `Segment.run b a c`, and `Segment.box` describe individual
bits, runs of length `a*n+c`, and the entire physical register file. Files have
at least nine blocks and an arbitrary finite spare suffix. A positive
decrement appends a zero spare. A box records at most one increment or
decrement effect, and the decrement branch names its physical register through
`Option (Fin 9 × Bool)`. Consequently an unrelated zero/nonzero assumption
cannot justify a decrement excursion.

`Represents` specifies the state, absolute head and every tape cell through
the existing `FiniteZipper.ZipRep`. It existentially quantifies the boundary
coordinate: a left-facing symbolic configuration has its actual head one cell
before that boundary. Exterior cells are false. The single explicit padding
cell inside `boxBits` agrees with the existing register proofs; it does not
truncate the represented tape.

`checkedStep` produces a target and a soundness proof. The proof field lies in
`Prop` and is erased from the executable `sstep` projection. Literal steps,
writing scans, peeling and recentering use exact zipper theorems. Register
excursions use the imported actual-table register proofs. Only a literal
transition sets the progress bit. `exec_sound` therefore proves positive
actual Core time when execution starts with progress false, even though a
zero-length scan or a recenter operation can consume zero literal time.
Actual execution time is existential; the theorem does not assert an affine
clock formula.

`isMatch` compares normalized segment syntax. Its proof merges affine runs
faithfully and removes only a far-left false run. Pointwise `getD` equality
proves that this removal preserves every exterior cell, including the cell
under the head in a left-facing view. Right tape, box effects, state and view
orientation still have to match. `exec_to_matches` and the certificate-facing
`verifies_sound` conclude positive whole-tape Core execution to the requested
target. `verifiesHalt_sound` concludes actual halting; the final write and head
move occur before state becomes `none`.

The source and seven main axiom audits passed with the absolute pinned Lean
4.32.0 binary. The only reported axioms are standard `propext` and
`Quot.sound`. Six concrete kernel certificate checks cover both branches of
site 000, break 001, increment 01010, continue 010111 and the unique halt site.
Additional checks reject a wrong named decrement guard and fabricated progress,
check affine left-padding normalization and different box effects, and verify
the actual halt write/right move. Two generic callers apply the results to
arbitrary gap parameters and register files. The final audit took 3.17 seconds;
the identical direct-lookup audit took 6.84 seconds.
Source hashes, commands and reusable audit source are preserved in
`results/symbolic-perm252-verification.json`.

The checked computational implementation looks up literal actions through the
already verified balanced `BootPerm252.fastMachinePerm252` table. Every action
used by a semantic theorem is explicitly transported by `fast_transition_eq`
to `machinePerm252`. The statement of Core soundness is unchanged.

The same scoped build freshly checked `BootstrapFramePerm252.lean` against
the existing checked 82,552-step boot proof and generic frame module. It did not
rerun that long proof. Dependencies came from the root's source-verified 105-module cache plus the frame module; this is not a fresh full source closure.

The Python audit's 8,391-case success has not yet been reproduced as 8,391 kernel
checks by this module. Source/successor linkage, the generic dispatch-frame
adapter, decoder/no-stray preservation and a full binary/RM halting simulation
remain separate obligations. No machine/nonhalting consistency calibration or
internal PA endpoint follows from this checkpoint alone.
