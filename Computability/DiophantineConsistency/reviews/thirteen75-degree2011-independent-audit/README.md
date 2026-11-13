# Independent exact degree of the 75-row 2011 graph

The read-only [audit](audit.py) exited 0 in both normal and optimized Python,
producing identical [receipts](CHECK.json); it uses explicit checks rather
than assertions. The [terminal observation](terminal-observation.json)
records the result. It pins the entire 75-row graph to commit `9294c63bd0`,
checks all rows and input ports are live, and counts 42 multiplications,
18 additions and 15 subtractions.

For the actual 2011 β, the audit proves an ordinary total-degree upper bound
of 96 using a tropical degree calculation and the exact cancellation
`(X+ac+γH)^2 − (a^2+H)c^2 = (X+γH)^2 + 2ac(X+γH) − Hc^2`.
It separately bounds every term involving K, MC or MF by degree 95. Setting
all thirteen variables to t and the other three ports to zero, with
`β = 2^(47·2011)−1` modulo 1,000,000,007, gives a nonzero coefficient
645917148 for `t^96`. Thus specialization to the actual other three ports
cannot change that top term, and the actual fixed-port graph has exact degree
96. Negative controls drop the top square, use a β residue that cancels the
diagonal top coefficient, and introduce a synthetic top-degree other-port
dependence.

The audit pins the current port-definition source bytes, all four full
compressed port payloads and their raw hashes, and compares them to the
previously captured Lean `#eval` outputs via their pinned receipt. That
captured evaluation is executable Lean plus external comparison, not an
internal equality theorem; its inherited Foundation and dynamic-provider
qualifications remain. The full fixed tuple is pinned even though the degree
argument needs only β and the other-port sensitivity bound.

The legacy `thirteen-unit-sphere96/audit.py` currently exits 1 on its stale
`ThirteenUnitSphere96.lean` source hash. This independent argument does not
execute or rely on that audit or its historical certificate. It establishes
an external exact degree for the pinned graph, not a Lean expression-to-graph
binding, a TeX decoder interpretation, an iPRA statement for that graph, or a
global minimum. The separate 75-node Lean binding is still required.
