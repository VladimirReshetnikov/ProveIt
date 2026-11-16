# PA194 seeded source-header dispatch prefix

`PA194SeedHeaderDispatch.twelveSteps` proves the physical path
`24→26→29→34→44→62→87→46→65→91→110→59→84` in every candidate PRA model.
The theorem takes an arbitrary model-valued left half and residual right tape;
its clock is the fixed numeral 12, and its input and output tape expressions
are explicit. Thus its parameters may be nonstandard, even though this is a
fixed-length physical trace.

The [model-uniform continuation to state 17](SEED-HEADER-TO17.md) also scans
the remaining header for arbitrary model-valued lengths and source files.
The [concrete state-15 checkpoint](SEED-HEADER-SCAN.md) records the corresponding
point in the blank-start run.

`modelSeedAt84` composes that path with the checked exact blank startup and
source-frame decomposition. At time 58,166 it has reached state 84 with the
stated left half, a 42-zero header, and the exact encoded source file including
all spare blocks. This is a prefix of the first seeded source instruction;
the separate 462-step fixed trace proves its concrete completion. Neither
result is an arbitrary model-length source-instruction simulation or a proof
of either PA consistency implication.

The module passed a suffix rebuild against retained prerequisite overlays,
including the two literal transition libraries; its printed theorem axioms
exclude `sorryAx`. `check-seed-header-dispatch.sh` repeats that suffix build,
checks selected source and direct-object hashes, and rejects `sorryAx` while
retaining unrebuilt transitive overlay dependencies. Those dependencies are not
claimed to have a fresh, complete closure audit.
