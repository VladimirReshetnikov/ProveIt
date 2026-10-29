# PRA multiplication equations: independent replay

29 October 2026. I read the complete theorem pair and checked the literal
binders and recursion direction. `PRAMultiplication` derives the universal
zero and successor recursion equations for the designated multiplication
symbol in arbitrary equality models of the candidate PRA, then uses
completeness to obtain closed object-theory derivations.

A fresh independent Lean 4.32 build, using `-M6000 -j1 -DElab.async=false`,
matches both author objects and complete logs. The main log is empty; eight
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
The [replay evidence](pra-multiplication-root-replay/) preserves all author
attempts and the independent driver, state and logs. Checked project parents
and inherited Foundation/Mathlib objects were reused, not fully rebuilt.
Standard-PRA compatibility and conservation remain open.
