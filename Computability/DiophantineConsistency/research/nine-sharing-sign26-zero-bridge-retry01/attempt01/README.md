# Sign26 zero bridge retry 01: partial failure

Author-observed outer session 72853 exited 1. The coordinate and conditional forward stages compiled; the reverse-gap helper failed with a type mismatch because concrete Fin-vector applications remained in the source term after `simp only`. The helper's printed report includes `sorryAx` and is error-contaminated; no helper or reverse theorem is proved and the last stage and postflight did not run. This diagnosis does not establish the cause of the earlier heartbeat timeout.

CoordinateDrop reports `lift_drop` and `drop_lift` with `[propext, Classical.choice, Quot.sound]` and two unused section-variable warnings. ForwardBridge reports `old_rows` with `[propext]` and `forward` with `[propext, Classical.choice, Quot.sound]` and no warnings. Monitor observations are sampled. The historical sign26 plan README appendix caveat applies.
