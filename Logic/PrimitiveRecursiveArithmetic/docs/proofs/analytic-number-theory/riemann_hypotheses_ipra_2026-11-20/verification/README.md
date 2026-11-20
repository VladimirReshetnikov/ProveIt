Lean 4.32.0 and the pinned Mathlib built the default project target successfully on November 20, 2026. The six checks in SmokePR.lean ran as part of this build.

From the package root, use `lake env lean verification/Audit.lean` to reproduce the declarations and Lean metatheory axiom inventory in `lean-audit.txt`. The `examples.txt` file is the stdout of `python3 check_packets.py` followed by `python3 check_packets.py 5 0 0 1 256`.
