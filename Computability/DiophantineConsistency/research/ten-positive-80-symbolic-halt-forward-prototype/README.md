# Conditional symbolic-port 80-zero to machine-halt direction

`TenPositive80SymbolicHaltForward.positive_zero_implies_halt` composes the
checked positive 80→90 output implication with
`DirectMainHalt.positive_model_iff`. In every IΣ₁ model it takes the three
explicit β/low/high equalities **and** the explicit equality
`integerPorts p = CompactSymbolicModelIff.p` for the complete target port
tuple. A positive 80 zero at that p then implies the internal machine halt
predicate. The tuple equality includes p₁ and is a real hypothesis of the
Lean theorem. In particular, the distinct retained external 80 K0 is not
silently identified with `paramKernel rho`.

This is only the graph-to-halt direction. It does not show a halt yields an
80 zero, prove iPRA derivability, or bind an external graph/PDF to the chosen
port tuple. The source tried a literal full-tuple specialization in retained
`observations/halt-attempt01/`; Lean hit its 3-GiB kernel memory limit there.
The accepted `observations/halt-attempt02/` uses the explicit tuple equality
and produced `/tmp/tenpositive-80symbolichaltforward-_y5xe_ef/Direct80SymbolicHaltForward.olean`,
SHA-256 `23d5936cf9afbd1518dd13ff306fd14f9484c1bafc0770af9b7a453a4c1e9c99`.
The runner enumerates both direct imports, verifies their selected ordered
LEAN_PATH paths and hashes before and after, and records their real paths.
It inherits the 90 halt and 80→90 provider boundaries and does not assert a
fresh audit of all transitive source-object, package or dynamic dependencies.
