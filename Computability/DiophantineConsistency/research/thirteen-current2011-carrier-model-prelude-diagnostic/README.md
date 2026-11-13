# Thirteen-variable model prelude diagnostic

This source is the exact prefix of the mechanically split carrier model
module, ending before the `complete` theorem. It includes the fixed port
lemmas, positivity and shifted-coordinate helpers. It imports the previously
checked generic core. It does not include or prove completion, the model
bridge, or either iPRA endpoint.

Actual outer session 66728 exited 0. Its dependency and compilation runs
both exited 0, with an empty compilation log. The isolated overlay runner
rechecked the authenticated seven predecessor outputs, their captured direct
guards, the generic core source/object/guards, and the routed direct inputs.
The output object SHA-256 is
`918f5fc28b61155bfc417f5ce50d1a5fde0023198c1b3779937768bbb9414bff`;
the retained [state](attempt01/state.json) SHA-256 is
`3846ce468421358eade614d2651a45d9db0037f0e46d303a92e7b54222d4fd2a`.
The source SHA-256 is
`c3a5c6047f9f72d7d5663fa2ad047f00754b5ea92208b6a04ae997714124acc8`;
the runner SHA-256 is
`6032eeb83e1b9f8f1f37bd08887eec1f6c4818397dd5fcbd900c29c9087b5949`.

The earlier complete remaining source failed at the interpreter memory
limit. This prefix passing places the failed work after the prefix, but does
not identify the exact failure point, since later elaboration can depend on
resource accumulation. The run used one worker, `-M2800`, a 180-second GNU
foreground timeout, low priority and memory/disk prechecks. It did not
provide automatic group-RSS or host-memory stopping or a dynamic/transitive
provider load trace. It is not a new clean rebuild of the provider closure.
