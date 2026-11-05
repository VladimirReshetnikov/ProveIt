# Factored thirteen-variable completion attempt

This draft retains the original `complete` statement and bridge statements,
but calls the separately checked `core_invariants` and `rank_ordinate`
helpers in place of their original local proof blocks. It imports the checked
model prelude. It has not passed Lean.

Actual outer session 50481 exited 1. The dependency run exited 0, but Lean
compilation exited -6 after 6.8 seconds with the interpreter memory exception
at `-M2800`. The full [state](attempt01/state.json) SHA-256 is
`a94c8290f5ab9cca618eb3707ce5ae2bbd795cece61e18799844de484e6b0fe5`;
the compilation log SHA-256 is
`824b2620890de367be1946e0b021b2bc8fc29572644815df8d65d0d2f6079421`. No successful completion object or endpoint was produced, and the
run did not reach its postflight. The source SHA-256 is
`62cd0c30993cc2f1a1f030cf5a1d65f6f2697545110d63c00190676837d872ae`;
the runner SHA-256 is
`269320eede4aa6a25b584fa9f1232bd90c461699fb690d7ad2b361ebb6b1d928`.
This failure does not show a mathematical error or isolate a particular
remaining declaration. It used one worker, a 180-second GNU foreground
timeout and prechecks, with no automatic group-RSS or host-memory stop.
