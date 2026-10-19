# Fresh check of the internal context calculus

The unchanged upstream [`R2Ctx`](Lean/ZFCinPA/R2Ctx.lean) proves context rules
for the literal numerical validator in every IΣ₁ model. Its hypothesis lists
and finite-set enumerations range over internal codes, including nonstandard
lengths. The checked interfaces cover modus ponens, hypotheses, deduction,
subsumption, shifted negated encodings and existence of enumerations.

The [actual check](results/r2ctx-verification.json) passed six named theorem
probes and ten typed callers. Source and audit took 27.201 and 2.006 seconds,
within a shared 120-second deadline, one thread, 4,096 MiB and default proof
limits. The axiom reports contain only `propext`, `Classical.choice` and
`Quot.sound`. The unchanged source has one unused-variable warning at line
343; the audit has none. No linter was disabled.

The guard selects 24 project source/object pairs from the successful native
GIC slots check, with seven inherited external boundaries and Init/Omega.
It checks those pairs, raw parent evidence and actual first providers. It
does not rehash the unrelated full ancestor tree or attest the complete
Foundation namespace overlay. The [guard and raw logs](r2ctx/),
[publication record](results/r2ctx-publication.json) and
[lossless history](r2ctx/history.json.gz) preserve that boundary and the
successful evidence; historical scratch paths remain explicit.

This is a fresh check of one prerequisite of R2. It does not replay the full
R2/R3 consistency equivalence or connect the validator to the binary machine.
The upstream introductory comment also lists `der_gen`, which is not defined
in this file; the current audit does not claim that interface.
