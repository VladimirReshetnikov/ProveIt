# Independent failure audit: macro recipe scoping

Author-observed outer session 15898 exited 1; this is not an independently observed raw process transcript. The dependency scan succeeded but Lean compilation exited 1 because `decide` could not synthesize `Decidable Norm38MacroRecipe.WellScopedTarget` for the named proposition. The emitted `sorryAx` report is from the failed declaration, not proof evidence. No successful scopedness object or final provider postflight was recorded.

`check.py` verifies source, state, logs, the direct audited recipe provider, 100 guard slots and 1,166 overlay links. No sampled stop or monitor error was observed. No Lean replay, scopedness or semantic theorem is claimed.
