# PRA addition equations: independent replay

29 October 2026. `PRAAddition` derives the universal zero and successor
recursion equations for the designated addition symbol in the candidate PRA
theory. I checked the literal binder and term order and the proof from the
actual code equations in arbitrary equality models; completeness then gives
closed Foundation derivations. This is not standard-model-only reasoning.

A fresh independent Lean 4.32 build of both files, with
`-M6000 -j1 -DElab.async=false`, matches both author objects and full logs.
Seven axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.
The [replay evidence](pra-addition-root-replay/) retains all nine author
attempts, including admitted probes 3–5 that are not in the final source, and
the independent driver, state and logs. Checked project parents and inherited
Foundation/Mathlib objects were reused without a full transitive rebuild.
Standard-presentation compatibility and conservation remain open.
