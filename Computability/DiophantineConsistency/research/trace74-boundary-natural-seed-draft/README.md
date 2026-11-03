# Standard natural finite seed interval draft

This unchecked source proposes to certify the seed's two strict inequalities `K*Y < C < K*Y+K` by ordinary Lean `decide`, then derives positive additive slacks. `S` is the audited finite partial seed; `X=2^31`, `Y=8*S`, and the recurrence uses the source ordinate offsets and indices 16 and 31. This draft imports the also-unchecked recurrence/cast bridge and has not been run in Lean.

The proposed `decide` proof is intended to be checked by the Lean kernel; its computation may exceed available memory or time. It does not use `native_decide` or establish a result dependent on trust in the native compiler. No proof, finite graph zero, fixed BFS tuple result or iPRA consequence is claimed until the relevant checks and theorem assembly have succeeded.

The [independent source review](../../reviews/trace74-boundary-natural-seed-draft-independent/README.md) verified the seed value, both ordinate conventions, and the interval via a separate Python computation. It does not establish Lean acceptance or a graph theorem.
