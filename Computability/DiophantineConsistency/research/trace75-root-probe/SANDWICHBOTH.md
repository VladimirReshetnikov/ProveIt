# Trace75 same-index shifted Pell sandwich

`Trace75SandwichBoth.graph_sandwich_both` proves in any IΣ₁ model with
β≥31, `MC<β`, `MF<2β`, and an actual positive trace75 zero that one `r>0`
has `R=rankNat=2r+1`, `X=2^R`, and both strict inequalities

`k*(X+1)^(2r) < 2*c*X^r < k*((X+1)^(2r)+X^r)`.

The proof shows the independently obtained first index equals `r+1`, uses
the actual `P=XY²`, and retains the shifted main parameter
`Y*(X+1)−1`. `K0` is arbitrary. This is not yet the binomial/population
conclusion or a halt/iPRA equivalence.

Accepted `run-sandwichboth-v2.py`, `observations/sandwichboth-attempt02/`:
Lean exit 0, no warning/error; object
`/tmp/trace75-sandwichboth-swsyrrxu/Trace75SandwichBoth.olean`, SHA-256
`9fdadd9aa0bf5288531f7a3692cd4958e7e8799633fcd5fd189ac816ef85d57d`.
Attempt 01 failed before elaboration on a missing transitive graph-power
provider. The accepted runner pins the added selected objects and historical
`ModelRatioBounds`; its known producer-time drift, coherent fresh-provider
rebuild, full transitive/package provenance and external graph/file binding
remain open.
