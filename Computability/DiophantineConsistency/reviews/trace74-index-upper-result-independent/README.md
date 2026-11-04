# Independent result review: generic upper bound on Pell indices

PASS for author-reported actual outer session 84149 exit 0, consistent with captured attempt04 stage PASS and Lean exit 0. Terminal SHA-256 `0f539f779805a678b238bb05abe1c1acc6fa4df6d0d295c159689e71edf794ea`, object `c5e744f44413bd6c5dc7ed40d228092d857da3d361cfaa2dca0595109200c918`. The runner, 24 recorded pins, source, object and logs rehash. Sole report is exactly `[propext, Classical.choice, Quot.sound]`, with empty stderr and no warnings.

The theorem is generic in an indicated IΣ₁ model and explicitly assumes X≥16,Y≥1,n≥2, c=kY+eta, k=eta+zeta with zeta>0, and both stated Pell ordinate identities. It concludes r<2n. It does not itself assert a graph-zero implication, index/rank equality, F/C bounds or guard. Prior attempts 01 (`09d97fa788533764e584c27599c72088e2a601e15a5265e896637eb5f6af6e2a`), 02 (`a2437a64e40197e7447eaa90d18809fa4508aa9bc1506da5c229660fbfd251dc`), and 03 (`c9bea4c7b995aa9949098776fd6c96c838698bf558a9b7ad7a1dbaed11d82ed9`) all exited Lean 1 with rejected sorryAx and remain excluded; targeted corrections and their saved post-exit source/runner bytes were reviewed independently.

This is an exploratory direct-pin result; full project/package/dynamic and historical source-object ancestry and future search-path shadowing were not comprehensively monitored. No Lean was run for this audit.
