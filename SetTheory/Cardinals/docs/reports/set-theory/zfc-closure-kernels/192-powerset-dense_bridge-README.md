# One absorbing invariant for the dense/zipper bridge

Baseline: `57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`.

This is a small, checked production-source simplification. It replaces only the
body of `SetTheory.BusyBeaver.ZFC.KDenseBridge.blank_iff`; all definitions,
lemmas, imports, theorem parameters and the theorem statement are unchanged.

## Reason for the change

The original proof performs two inductions over time: the forward direction
builds either a sparse halting witness or a live pair of related runs, and the
reverse direction separately reconstructs the live-run relation. The first
induction already knows when the dense machine halts. Retaining that witness
lets the same induction handle both directions.

For every time `t`, maintain the invariant

```
(BlankHalts D ∧ Halts M sparseInitial) ∨
  ∃ z, run M t sparseInitial = some z ∧ Rel ex H (D.run t) z.
```

The left branch is absorbing and carries the result in both representations.
The right branch means a corresponding sparse configuration is still present;
it can already be terminal. Dense halting freezes the total run, whereas the
sparse run becomes `none` only on the next attempted step.
The right branch advances using the existing `rel_step`; if the dense run is
halted, the existing `rel_halt` establishes the left branch. For the reverse
implication, evaluate this invariant at the supplied sparse halting time. In
the live branch, determinism identifies its sparse configuration with the
supplied one, and `rel_step` rules out a live dense state. There is no new
simulation hypothesis or new axiom.

## Measured change

| Scope | Before | After | Reduction |
|---|---:|---:|---:|
| Entire source, physical lines | 193 | 178 | 15 (7.77%) |
| Entire source, bytes | 8,127 | 7,527 | 600 (7.38%) |
| `blank_iff`, physical lines | 52 | 37 | 15 (28.85%) |
| `blank_iff`, bytes | 2,230 | 1,630 | 600 (26.91%) |

Counts include the two explanatory comments in the replacement. The new
source is a readable induction proof, not a compressed tactic expression.

## Verification performed

Official Lean 4.32.0, commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`, successfully checked the unchanged
`BusyBeaver.Core` and `KZip` dependencies, the original and modified dense
bridge, and `Audit.lean` against each version. The audit checks the original
public statement verbatim and prints its axiom dependencies. Both versions
report exactly `[propext, Quot.sound]`; neither reports `sorryAx` or
`Classical.choice`.

This targeted check does not claim a fresh build of the complete
`KEndpoint215` closure. Every downstream use receives the same theorem type.
The machine table, source program, certificates and ZFC-calibration proof are
untouched.

## Integration and reproduction

Apply `dense_bridge.patch` at the repository root, or replace the corresponding
module with `BusyBeaver/ZFC/KDenseBridge.lean`. Before integration, run:

```
python3 verify_dense_bridge.py --repo /path/to/ProveIt \
  --lean /path/to/lean-4.32.0/bin/lean --work-dir /tmp/dense-bridge-check
```

The script obtains the exact baseline files from Git, builds both variants in
isolated directories, checks source hashes and the unchanged signature, and
compares the axiom audits. It never modifies the repository. No Mathlib cache
or previously compiled project modules are needed for this targeted check.

This invariant is also a useful review pattern for other deterministic
representations: when both directions of a halting equivalence reconstruct
the same synchronized run, retain both terminal witnesses in one absorbing
case before introducing another run induction.
