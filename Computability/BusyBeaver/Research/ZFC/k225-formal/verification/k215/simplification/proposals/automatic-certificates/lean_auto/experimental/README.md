# Resource experiment; not an accepted final proof

`DefinitionalAutoData.lean` is the first implementation of the generated
relation. It defines every block by reducing `inferredRows`, so generation is
repeated during kernel checking. The first three 90-entry blocks compiled;
block 3 (the fourth) exceeded the explicit 3,000 MiB limit.

`definitional_receipt.json` and `memory_limit.log` preserve that failed run.
They do not constitute a complete concrete theorem. The generic soundness
theorem and the executable full acceptance check passed independently.

`staged_memory_limit.log` records a later resource limit at block 6 while
checking the materialized cache with the same 3,000 MiB cap. The staged build
continued with a 4,000 MiB cap. Its unsplit block 11 also exceeded that limit;
`UnsplitCheck11.lean` retains the rejected proof script. The final blocks
11 through 15 use the incoming normalized proposal's quarter-block tactic.
Source/object/log identity of successful earlier modules was checked on resume.
The accepted receipt keeps the failed attempts separate.

The active build uses the staged source and the larger default cap. None of
these resource failures is a mathematical counterexample to the correspondence.
The exact timing and memory limit are host-dependent.
