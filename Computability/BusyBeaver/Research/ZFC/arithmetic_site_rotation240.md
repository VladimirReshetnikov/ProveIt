# Internal execution of every Rotation240 instruction

[`ArithmeticSiteRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticSiteRotation240.lean)
connects the complete finite site coverage to the concrete arithmetic symbolic
executor and the canonical numeric frames. Every accepted instruction has a
positive binary execution clock in every IΣ₁ model. Register values, extra
spares and gaps remain arbitrary internal values, and the conclusions identify
the complete configuration.

The six source endpoints cover increment, both decrement branches, break,
continue and halt. The five returning cases reach the exact `nextControl` of
the checked catalogue with the file update used by `ArithmeticControlStepRotation240`.
Increment adds one spare. Positive decrement preserves the spare count and
adds one padding cell. Halt reaches state code zero. Actual coverage and all
four concrete box contracts are discharged; no runtime premise remains.

The [actual check](results/arithmetic-site-rotation240-verification.json)
passes 15 axiom probes and 15 typed callers with zero warnings and only
standard axioms. Source and audit took 3.144 and 2.551 seconds, respectively,
at default proof limits, sharing 120 seconds with one thread and 4,096 MiB.
The selected prerequisite closure contains 699 project modules, with actual
SiteValues, BoxRuntime and ControlStep checks as its direct parents. No
dependency family was rebuilt.

The [publication record](results/arithmetic-site-rotation240-publication.json)
binds the accepted source, audit, logs and guard. The
[history](arithmetic-site-rotation240/history.json.gz) preserves the source and
guard preparation, including its metadata correction. The subsequent
[control simulation](arithmetic_control_simulation_rotation240.md) and
[blank-control composition](arithmetic_blank_control_rotation240.md) now
connect these endpoints to unbounded iteration and the exact startup.

Attribution remains with Mira-Cult, Jeff Ketchersid, Andrew James Wade and
ProveIt, as recorded by the underlying machine and source artifacts.
