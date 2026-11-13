# Both scaled Pell sandwiches for the same graph rank

`Direct80SandwichBoth.graph_sandwich_both` proves in every IΣ₁ model that an actual positive zero of the exact Lean 80-row graph has one internal positive `r` satisfying `rankNat=2r+1`, `X=2^(2r+1)`, and **both** strict scaled inequalities `k*N<2*c*D<k*(N+D)`, with represented powers `N=(X+1)^(2r)` and `D=X^r`. The explicit hypotheses are `beta≥31`, `MC<beta`, `MF<2*beta`, and internal odd beta.

The proof retains the same `r` from the checked lower sandwich, synchronizes the first index through its proved exact alignment, derives the upper shifted-scale coefficient and perturbation/crude bounds from actual graph factors, and applies the independently checked upper Pell sandwich. It does not invoke an unscaled sandwich at a mismatched base or assume the half-binomial conclusion.

Guarded author `observations/attempt02/` passed without diagnostics, yielding `/tmp/tenpositive-80sandwich-both-8074dg0f/Direct80SandwichBoth.olean`, SHA-256 `846409e5f34d538cf649d304af8f52569a630a02e3f40048d56d10db17bb89ef`. Attempt01 halted on a missing selected module and is retained. Printed axioms are `propext`, `Classical.choice`, `Quot.sound`. The runner pins selected prototype objects and direct sandwich/ratio providers, not the complete transitive project/package/dynamic or historical source-object ancestry. Resource checks are sampled; no paired replay is claimed.

The integer rounding join, fixed-recipe source reconstruction, graph-to-halt equivalence and iPRA endpoint remain separate.
