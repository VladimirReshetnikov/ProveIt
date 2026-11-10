# Independent sign23 Delta coordinate failure audit

The author observed outer session 90674 exit 1. The independent checker
exited 0 and saved `result.json`. It checks the source and logs, both direct
squares providers, guard slots, overlay links and upstream audits.

Lean's dependency scan succeeded but compilation exited 1 at an unsolved
embedding simplification goal involving `ι 4` and `ι 3`. The failed log's
`delta_zero` axiom report contains `sorryAx`. There is no object or final
postflight, and no Delta-coordinate theorem is claimed from this run, even
though other printed axiom reports lack `sorryAx`. Provider guards are point
observations and Lean was not independently replayed.
