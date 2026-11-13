# Source-only Lean draft for the 95-gate rewrite

`Sign14Optimized95.lean` proposes alternate staged syntax for the two audited
external ring rewrites: a new shared07 and its six dependent nodes, plus the
factored Nt row. It states generic commutative-ring evaluation equalities for
the changed rows and their five-square seed. The other row is reused unchanged.

An [independent source review](../../reviews/nine-sharing-sign14-95gate-lean-draft-independent/README.md)
checked that the expanded proposed rows match the pinned external 95-gate AST.
This is source-only: elaboration, the equality theorems, the iPRA endpoints,
exact degree and JSON/PDF/file semantics have not been established for it.
