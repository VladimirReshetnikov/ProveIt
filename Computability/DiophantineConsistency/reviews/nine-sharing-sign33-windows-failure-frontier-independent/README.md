# Independent failure audit: sign33 windows

Author-observed outer session 50522 exited 1. The dependency scan succeeded and Lean compilation exited 1 because `absdiff` was unresolved in the theorem statement. The axiom report includes `sorryAx` for the failed declaration; it is not proof evidence. No successful object was emitted and final candidate-guard and producer postflight checks were not reached. The outer record is an author observation, not an independent process transcript.

The retained source, failure state and logs, two selected direct producer bindings, 150 direct guard slots and 1,162 overlay links were checked by `check.py`. No monitor stop or error was recorded; resources are sampled. This audit does not replay Lean or establish the windows theorem.
