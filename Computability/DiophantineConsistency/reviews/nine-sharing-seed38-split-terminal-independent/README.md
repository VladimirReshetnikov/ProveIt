# Independent terminal review of the split norm38 seed experiment

The post-hoc author record reports outer session **55616, exit 1**; this
reviewer did not observe that session directly. The retained state records four
successful dependency scans and compiles: `SharingGateModel`,
`ForwardWitness38`, `SharingSeed38Syntax` and `SharingSeed38Normalize`.
The checked normalization theorem says that, for an integer port tuple with
positive first port and every integer distinguished input, the literal seed
evaluates nonzero at zero witnesses. It is generic in the port tuple; it does
not itself instantiate the actual ports or prove the model zero bridge.

The next stage, `SharingSeed38Weighted`, exited **1 without a monitor stop**
after about 118.6 seconds. Its retained Lean log reports unsolved
`Expr.weightedDegree` goals. This was a Lean proof failure, not a timeout or a
mathematical disproof of the degree bound. The five subsequent stages did not
run, so the polynomial-degree theorem, graph bridge and endpoint remain open.
The gate compile retained two unused-simp-argument warnings; no axiom reports
were requested in this experiment.

`check.py` compares the four syntax definitions and three normalization
declarations with the original separately reviewed seed source, pins all ten
split sources, verifies the five attempted stage logs and source snapshots,
the four successful object hashes, 500 direct guard slots, and 1,055 overlay
links. Failed-stage guards are snapshots before the failing compile; the final
all-stage guard audit did not run. The external seed AST review remains a
separate prerequisite for the source correspondence.

These are retained-evidence and live provider point checks; no Lean process
was run by this review. The recorded outer receipt is an author record, not a
raw transcript or an independently observed exit. Inherited package/dynamic
dependencies and sampled resource limits retain their documented caveats.
