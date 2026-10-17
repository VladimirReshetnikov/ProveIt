# Actual second read and the two-read dispatch entry

`ArithmeticControlReadTemplate254.lean` proves a reusable finite read shape and binds it to the actual second read of literal `Prog254`. `p1Read` uses catalogue controls 24–37 and exits at control 38, path 11100, the actual dispatch decrement of logical register3. Its output target is parameter1/D, physical field3.

`ReadShape` supplies finite controls and literal source/continuation equalities in the current actual catalogue. Its target field must be distinct from PL and both scratch fields. These are finite diagram conditions, with no execution or runtime premise. The all-internal generic proof discharges the three transfer loops, the Cantor walk body, bounded fixed-file Σ1 reachability, scratch restoration and a positive terminal logical time. The actual `p1Read` constructor proves every diagram condition by literal equality, closing all premises of `read_p1`.

For every IΣ1 model and arbitrary internal nine-register file with both scratch fields zero, `read_p1` replaces PL by `second(oldPL)`, adds `first(oldPL)` to D, and preserves all other fields. The shared proof imports the already checked IOpen Cantor inverse-successor laws. It makes no standard-counter assumption and uses no universal-files/existential-runtime induction principle.

`reads_run` composes the actual first and second reads at their common control24. Starting at control10, it reaches dispatch38 after a positive internal logical time, with AC=`oldAC+first(oldPL)`, D=`oldD+first(second(oldPL))`, and PL=`second(second(oldPL))`. The full original file remains explicit; the other six fields are preserved. In particular both scratch fields remain zero. The theorem permits arbitrary initial AC and D, with a focused AC=0 caller matching the command-decoding boundary.

The proof does not infer this composition from a naive renumbering or terminal step conjugacy. Both actual macro durations and endpoints are independently proved and then composed by the checked run-additivity law. It does not need a new first-exit assumption.

The first source/audit attempt passed: 12 ordered axiom probes, 15 generic and specialized callers, standard axioms only, zero warnings. Source compilation took 11.697 s and the audit 2.319 s. The guard checks 91 exact project prerequisites, 6 external boundaries, 205 inputs and the fresh object. Source limits are unchanged defaults. No dependency is built or downloaded, and neither native site certificates nor the bootstrap are replayed.

The portable checker is byte-identical to its successful executed driver:

```bash
python3 Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_read_template254.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/Proofs \
  --read-evidence /path/to/Proofs/Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-read254-verification.json \
  --output /outside/Proofs/read-template-check
```

Add `--prepare-only` for metadata validation against existing pinned Foundation/Mathlib objects. The separate maintained-default preparation is UNBUILT, with no proof replay or additional controls.

This closes the two actual reads immediately preceding dispatch. Dispatch branches, constructor routines and their composition with the represented Enum scheduler remain to be connected on arbitrary internal inputs. The clocks count numbered register instructions; binary-time transport remains a separate checked result. This module claims no complete internal L2/Enum equivalence, whole PA consistency equivalence, or state reduction.
