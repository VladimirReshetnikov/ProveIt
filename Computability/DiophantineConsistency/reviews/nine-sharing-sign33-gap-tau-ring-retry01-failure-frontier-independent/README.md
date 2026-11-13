# Independent failure audit: gap/tau additive orientation

Author-observed outer session 52147 exited 1; this is not an independent raw process transcript. The dependency scan passed, but Lean compilation exited 1 on two addition-order mismatches: the available inequality has `alpha+F ≤ q-F+F`, while the rewrite seeks `F+(q-F)`, and `le_add_self` has the opposite orientation to the requested `r≤r+2`. The emitted axiom report contains `sorryAx` from the failed declaration, not a valid proof. No successful object or final postflight was recorded.

`check.py` verifies the pinned source, state and logs, selected direct dependencies, all 150 direct guard slots and 1,164 overlay links. No monitor stop/error was observed; resources are sampled. No Lean replay or sign theorem is claimed.
