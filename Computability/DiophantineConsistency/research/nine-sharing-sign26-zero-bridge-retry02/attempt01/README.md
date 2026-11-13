# Sign26 zero bridge retry 02: passed

Author-observed outer session 37631 exited 0. All four stages and final postflight passed. `old_rows` and `new_rows` report `[propext]`; `lift_drop`, `drop_lift`, `forward`, `reverseGap`, and `backward` report `[propext, Classical.choice, Quot.sound]`. CoordinateDrop emitted two unused section-variable warnings; the other stages have no warnings.

This establishes the symbolic-port forward and backward zero bridge in IΣ₁: forward requires explicit p0/p1 cast hypotheses and beta at least one, and backward obtains both gap and q3 equations from old zero. It does not establish a source equivalence, endpoint, Lean degree result, or external JSON binding. Monitor observations are sampled. The historical sign26 plan README appendix caveat applies.
