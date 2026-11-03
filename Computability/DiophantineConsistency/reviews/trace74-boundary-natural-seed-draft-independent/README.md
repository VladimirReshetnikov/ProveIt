# Independent source review: finite natural seed draft

This is a source-only review of `research/trace74-boundary-natural-seed-draft/Trace74BoundaryNaturalSeed.lean` SHA `d94229597d11921a7fb0a174334b6ff497836301e1a0a39ecbb8020f5a5d33f0`. It imports the **unchecked** recurrence-cast draft. No Lean result is asserted, and `decide`, `omega`, tactic availability and resource costs remain untested.

We independently checked that S's hexadecimal numeral matches the retained Python finite seed. With X=2³¹, Y=8S and P=XY², the first offset is `2*(P−1)+1 = 2P−1` because P≥1; the offset recurrence's usual base is therefore `2P+1`, used at index 16=r+1. The main offset is `Y*(X+1)`, giving usual base `Y*(X+1)+2` at index 31=2r+1. These match the Python seed's source interval, not its distinct actual-ordinate base one lower. An independent Python calculation rechecked `K*Y < C < K*Y+K` under these definitions. The `slacks` statement is the natural subtraction decomposition of that interval; its proposed Lean proof is unchecked.

This finite arithmetic comparison is not a kernel-checked certificate, a model-cast instantiation, or a graph zero. It does not discharge the remaining parametric seed phase, exponential, growth, positivity and model Pell equations, establish fixed BFS ports, or prove an iPRA conclusion. The independent check is in this review directory; no Lean was run.
