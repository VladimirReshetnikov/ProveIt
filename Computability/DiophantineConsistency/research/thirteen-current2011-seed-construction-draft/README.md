# Fresh seed-construction helper attempt

This draft extracts the strong, auxiliary and positive-carrier witness block
from the thirteen-variable completion proof. It asks for the original model
bounds, rank phase, rank ordinate, and positive/divisible transport, and
returns positive ring witnesses with the strong norm and auxiliary residual
needed by `replace_zero69`. It imports the separately checked core-invariants
helper. The draft is not checked and does not establish completion.

Actual outer session 22429 exited 1. The dependency run succeeded, but the
compile run reached the 180-second timeout (nested exit 124), with an empty
compile log and no accepted output or axiom report. The [state](attempt01/state.json)
SHA-256 is `583be8cc8e53eb7f0827cc1fe29547ced8a3b40d89cf5ec6fd332654428c10a6`;
the source SHA-256 is
`06f00485f5991ff193561f2d6c5da33e11ba554f7a75247534f04ffe421752f1`;
the runner SHA-256 is
`72dbeae7f51bdcc92ff89f0f4f9bd9ad1d98f6ade526c07e5cf73602760c4b1e`.
This timeout does not establish a mathematical error or isolate a failing
proof step. The run used `-M2800`, one worker, GNU foreground timeout,
low priority and resource prechecks, without automatic group-RSS or
host-memory stopping. It did not reach the postflight.
