# Standard natural finite seed interval draft

This source certifies in the author check the seed's two strict inequalities `K*Y < C < K*Y+K` by ordinary Lean `decide`, then derives positive additive slacks. `S` is the audited finite partial seed; `X=2^31`, `Y=8*S`, and the recurrence uses the source ordinate offsets and indices 16 and 31. The recurrence/cast bridge passed Lean and independent audit. The finite interval author check passed; its [independent post-run audit](../../reviews/trace74-boundary-natural-seed-result-independent/README.md) passed.

The successful check uses ordinary kernel `decide`, with no reported native compiler axiom. It establishes the natural interval and its slacks; it does not establish a finite graph zero, fixed BFS tuple result or iPRA consequence.

The [independent source review](../../reviews/trace74-boundary-natural-seed-draft-independent/README.md) verified the seed value, both ordinate conventions, and the interval via a separate Python computation. It does not establish Lean acceptance or a graph theorem.
