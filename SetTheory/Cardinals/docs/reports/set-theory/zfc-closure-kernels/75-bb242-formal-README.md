# Relative Lean proof of the 242-state machine

These four modules use Lean 4.32.0 and its standard library. They do not use Mathlib. The main theorem is `BranchBorrow242.start95_halting_iff`: for every integer head position and every binary tape `Int → Bool`, the inherited 243-state table halts from state 95 exactly when the new 242-state table does. The tape may have infinite support. Blank-tape halting and nonhalting follow as special cases.

The statement is a relative machine theorem. `calibration_transfer` transfers any stated consistency calibration of the 243-state machine to the new machine, with that calibration retained as an explicit premise. The full logical/source proof of the inherited machine is not imported by this standalone package.

## Exact machines and counting convention

`Tables242.lean` contains two independently rendered arrays, each with indices 0 through 255. **Inherited label 255 is a working state and is included.** The unused index 254 is the designated halt state. Absent working labels have `none` entries. There are 243 present pairs in the old array and 242 in the new; each present pair supplies both binary transitions. Both counts are kernel-checked theorems.

The transition function makes the halt configuration absorbing when it is extended to a total iteration function. Halting means reaching designated state 254. This convention permits finite-trace reasoning without changing the machine's halting event. The delivered canonical table relabels inherited start 95 as canonical start 0 and inherited halt 254 as canonical halt 242; the table-binding and renumbering checks belong to the accompanying machine verifier.

`verify_formal.py` independently parses every array element and compares it with the supplied `.tm` files before invoking Lean. It checks all 486 old rows and all 484 new rows, including inherited state 255. It also verifies that the new table is precisely the deletion of state 15 and the two advertised overrides.

## Proof structure

`BlockSimulation.lean` proves a general positive finite-block simulation theorem. Related checkpoints need not advance at the same speed. If both machines take a positive finite number of transitions to the same next checkpoint, and their terminal configurations are absorbing, they have the same halting behavior. An induction on a halting witness's transition count proves both directions. In particular, no unproved assertion about infinite traces or fairness is used.

`Reduction242.lean` proves the invariant

- in states 18, 47, and 65, the cell immediately left of the head is zero;
- in state 27, the scanned cell is zero.

The invariant is proved for the complete old table by the exact finite incoming-edge facts. It holds at state 95 for arbitrary head and tape. Checkpoints satisfy this invariant and exclude deleted state 15.

Every ordinary checkpoint advances by one identical transition in both machines. At state 11 reading zero, the old machine takes two transitions. If the right neighbor is one, the new machine also takes two transitions and reaches state 22 two cells to the right. If that neighbor is zero, the new machine takes four transitions and reaches state 21 two cells to the right. Both local lemmas prove equality of the entire resulting tape; all writes reproduce already present bits. The old invariant supplies the next checkpoint, and the generic theorem closes the comparison.

## Reproduction

From the artifact root, with official Lean 4.32.0 available as `lean`:

```sh
python3 formal/verify_formal.py --output /tmp/zfc242-formal-replay
```

Use `--lean /absolute/path/to/lean` when needed. The output directory must be fresh. The script copies the four source files into it, compiles all modules into a separate object directory, and records every command and output. A successful run requires 18 named axiom reports, 13 typed callers, zero warnings, no custom axioms, and unchanged inputs after execution.

All reported dependencies are contained in `{propext, Quot.sound}`; the finite incoming-edge facts, patch equality, and state counts have no axioms. The source contains no admitted proof or native decision shortcut. `Tables242.lean` raises only the finite compilation resource limits to recursion depth 4096 and 2,000,000 heartbeats; the other modules retain their defaults. No compiler setting changes the logical axioms.

To reproduce the literal arrays from the pinned old machine without overwriting the delivered source:

```sh
python3 formal/generate_tables.py --output /tmp/Tables242-regenerated.lean
```

The generated file is byte-identical to `formal/Tables242.lean`. The original finite tables and program retain the attribution and licenses recorded in the research report.
