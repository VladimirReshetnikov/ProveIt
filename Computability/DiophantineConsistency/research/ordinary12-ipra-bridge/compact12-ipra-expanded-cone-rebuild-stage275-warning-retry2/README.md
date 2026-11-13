# Stage 275: rejected receipt-routing setup

This attempt used the corrected rejected-object hash and quarantined the exact
stage 275 object. Before invoking Lean, its merged-build check stopped because
the runner routed stage 273's receipt but omitted stage 274's already
successful receipt from the same packet. The actual stage 274 object therefore
appeared as an unexplained extra. No Lean compile ran. The raw runner output,
baseline, mutation tests, monitor and quarantine receipt are retained. A fresh
retry must route both stage 273 and stage 274 to the earlier packet and verify
the existing quarantine before compiling stage 275.
