# Independent review of the uncompiled norm38 model draft

`check.py` independently interprets the concrete Lean assignment as pairs of
free commutative integer polynomials, then checks its 81 nodes and all 60
ordered gates against the pinned current graph and seed. For each materialized
gate, both component residuals are compared with the seed polynomials; absent
negative components are checked to vanish. Every inline gate has zero
component residual by construction. The five terminal value-minus-target
polynomials also match the corresponding seed residuals. Thus all 29 residual
polynomials match externally, including their order; the resulting targets are
N0 at 61, N1 at 44, Na at 78, Nt at 66, scaled_Ns at 80, with Delta at 36.
The assignment uses `w 0` for seed coordinate 1 and `w 37` for seed
coordinate 38; a Lean specialization still needs the corresponding map from
`Fin 39` that skips distinguished coordinate 0.

The generic `constantTrace` statement explicitly assumes both component
residuals for every gate. Its conclusion is a trace from the final assignment
to itself, which is mathematically valid because that assignment satisfies each
gate; it does not itself prove agreement with the source graph's ordinary
evaluation. `ringStep_extends` requires agreement on both inputs, a reference
gate equation, and target freshness; its stated conclusion follows from these
conditions. The sum-of-squares extraction is valid in the ordered difference
ring under its model assumptions. Its generic proof body closely matches the
checked `NineLightQuartic` predecessor, but its import context and seed-specific
corollary have not been checked here. No false mathematical statement was
found in the draft statements.

This review is external and source-only. It does not check Lean elaboration,
the imported providers or proof scripts, the reduction of literal residuals
to `gatesHold` and `fiveNorms`, topology inside Lean, source evaluation,
fixed-port casts, the ordered norm theorem, Jones instantiation, or iPRA
endpoint. The pinned packet accurately marks these obligations and does not
claim them solved. `check.py` pins all three Lean files, the graph and the seed;
run it with `python3 -I -S -B`. No Lean process was run.
