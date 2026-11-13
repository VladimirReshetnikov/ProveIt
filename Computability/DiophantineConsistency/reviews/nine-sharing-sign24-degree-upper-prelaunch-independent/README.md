# Independent sign24 Lean degree-upper prelaunch review

Checker session 70348 exited 0. It verifies the two source/draft/manifest
hashes and ordered imports, the structural degree convention (constants 0,
variables 1, add/sub maximum, multiplication sum), and the intended bound on
`Expr.toPolynomial.totalDegree`. The concrete source proposes syntactic
degree exactly 8 and polynomial total degree at most 8 for **arbitrary
integer ports**, then specializes to current ports. It checks the current
expression provider survey and final recheck hook, reruns expression and
bridge audits, and runs the no-Lean preflight.

This is a proposed Lean theorem, not a checked degree result. Syntactic
degree 8 is an upper-bound computation, not an exact polynomial lower bound;
the external JSON/byte and PDF bindings are separate. The scoped `-M3600`,
sampled 4 GiB RSS and inherited point-provider ancestry limits remain, and
the runner requires the exclusive slot.
