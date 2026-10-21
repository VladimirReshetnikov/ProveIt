# Recovery and selected checks for batch 194

Recover the original `673c87a878` archive into a new directory outside the
repository:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover-intake194.py /tmp/intake194-recovered
```

This restores all 57 members without executing supplied code. The tested
[recovery receipt](data/intake194-recovery.json) and
[placement map](data/intake194-placement.json) preserve every original name,
including article/PDF and the exact historical parent archive. Placement
`7fff7bc909` retires the ZIP. The inner packet directory is:

```text
/tmp/intake194-recovered/K217_Exposed_Marker/K217_Exposed_Marker
```

Run the three source-reviewed leaves on a fresh disposable copy, with Python
assertions enabled:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake194-fresh/run.py \
  --packet /tmp/intake194-recovered/K217_Exposed_Marker/K217_Exposed_Marker \
  --output /tmp/intake194-three-fresh
```

The adapter retains the original executed runner under `history/`, with an
explicit path-only diff. It creates a copy, removes only the fixed-core
verifier's initial provenance-manifest loop, saves its original code and
exact narrow diff, then executes reconstruction, independent four-case fold,
and fixed-core emitter in order. Every child has a 60-second wall cap; a
failed child stops the driver. It checks the four rebuilt artifacts against
the original, the local-proof status and negative control, and the complete
fixed-core receipt against the delivery. It writes raw stdout/stderr and
actual argv, status, elapsed time and outputs. The portable adapter itself
was source-reviewed; the historical runner performed the recorded execution.

The [actual result](data/intake194-fresh/actual.json) and
[independent saved-result audit](data/intake194-fresh/review/actual-review.json)
record three passing jobs in 1.796 seconds. All mathematical fixed-core
assertions remain unchanged. No checksum manifest, omnibus wrapper, parent
calibration, complete startup, universal runtime or proof-assistant job ran.
The full ordinary [review](data/intake194-fresh/review/dossier.md) separates
the main machine from the optional axiom/source experiment.

The [own isomorphism reader](data/intake194-fresh/comparison/review_data.py)
and [complete mapping receipt](data/intake194-fresh/comparison/review.json)
compare all transitions, canonical labels and source roles. Its historical
absolute input paths are preserved as provenance, not instructions to reuse
those scratch directories. The table equality under relabeling transfers the
accepted Source-152 machine semantics, including its already fresh runtime
and startup. The new package's large runtime/startup files are retained
**delivered evidence**, not fresh runs by this intake.

[The comparison note](intake-194.md) gives the three-state map, explains why
the savings do not stack and states every fixed-core compiler/allocation
limitation. The [public alternative presentation](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k217/presentations/exposed-marker/README.md)
provides its native and breadth-first compact tables with attribution.
