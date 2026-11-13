# Independent review: symbolic rank-node failure

The retained dependency check exited 0 and Lean compilation exited 1 when `rfl` failed to close the raw evaluator equality. The separate author record says session 2128 exited 1. The axiom report contains `sorryAx` and is error-contaminated; no successful stage object was produced and the second stage did not run. Full-run postflight was not reached.

The checker validates the source, state, logs, author observation, two selected carry producers, 150 recorded guard slots and 1,181 overlay links. No Lean replay was made. The outer record is not an independent raw terminal transcript; provider checks are point-in-time and monitoring is sampled.
