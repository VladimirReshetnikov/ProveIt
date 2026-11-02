# Heuristic three-gate serial screen for the 13-variable circuits

This packet adapts the earlier [87-gate serial probe](../adaptive-first-root-factor87/SCREENING-THREE-SERIAL.md)
to the current pinned 87-operation square-sum and 86-operation product graphs.
Both executions reported no lower-live-gate candidate and actually exited 0.
This is a **heuristic observation**, not an exhaustive lower bound, a new
equation, or a Lean theorem.

For one target row at a time, the script screens three new binary operations
in the serial shape `t1 = a op b`, `t2 = t1 op c` or `c op t1`, and
`target = t2 op d` or `d op t2`, with `op` chosen from `+`, `-`, `*`.
All `a,b,c,d` are original inputs, original gates earlier than the target,
or literals `0,1,2,3,4`. Other rows and their ordering stay fixed. It uses
three deterministic modular signatures with seed `80281234` and modulus
`2305843009213693951`; a sampled match would still require exact polynomial
verification and liveness/witness review.

It inspects only targets whose replacement by `0+0` makes at least three old
rows dead in the output DAG. Multiplication inversion skips any operand with
a zero sample; possible candidates in those cases are not examined. The probe
does not cover fork-shaped or more general three-gate expressions, reusing a
new temporary twice as an operand, four or more new gates, simultaneous
changes to multiple targets, later-node reorderings, other literals, alternate
positive-witness encodings, fixed-port-only identities, or zero-set
equivalences that change the target polynomial. No global minimum claim is
made. The later [bounded one-/two-gate certificate](../frontier13-local-rewrite-screen/README.md)
has a different, explicitly fail-closed scope; this three-gate probe does not
inherit that stronger conclusion.

`run.py` records the graph/script input hashes, complete stdout and actual
subprocess exit for each execution, and the deliberate optimized-mode
rejection. It refuses to overwrite its receipt. Run `screen.py` with either
pinned graph path for a read-only repeat, or execute `run.py` in a copy without
the saved receipt.
