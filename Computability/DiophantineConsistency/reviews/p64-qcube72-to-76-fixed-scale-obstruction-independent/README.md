# Independent review: conditional 72-to-76 fixed-scale obstruction

**PASS within captured-provider scope.**
[`no_fixed_scale_target`](../../research/p64-qcube72-to-76-fixed-scale-obstruction-draft/FreeMain72To76FixedScaleObstruction.lean)
works in an arbitrary IΣ₁ model. Its premises include positive source 72 and
target 76Y zeros at the same fixed `compactPorts K`, source `3|q`, and
equal X,Y,c,k. Its conclusion is False under those premises. In particular,
it does not assume equal q, assert that a source zero exists, or rule out
an existential target with changed scale.

The proof reconstructs the checked 76Y forward conversion explicitly: a
positive gap h updates only target coordinate 13, yielding a positive 72
zero while retaining q,X,Y,c,k and rank. The difference-ring gap identity
becomes the actual carrier `h+k=Y²*gamma+(R+1)` using the target's
original coordinate 13 as gamma. The checked two-zero obstruction then
applies to the original source and the updated target; all four equality
hypotheses are transferred through the update. This is an all-model Lean
composition, not the earlier merely external rigidity argument, but it is
conditional on both zeros and the displayed equalities.

The retained attempt01 log/result match their temporary originals, with
recorded Lean exit 0, no stop and the expected axiom report. The output
object and both direct provider identities match their recorded hashes.
Independent [check.py](check.py) ran exit 0 and rechecked all 42 direct
input, companion and shadow guards; [result.json](result.json) records the
result. No Lean replay or transitive/dynamic ancestry audit was run; sampled
monitoring limits are inherited.

Checker SHA-256
`9384949b2009e47dad95b3c7b38689ec86d962dd966f64a8d3ea59147bd2a002`;
result SHA-256
`7802dddbcb7932c4af5a5fda0ca63a978a74943397272b21a216f7030ce58d00`.
