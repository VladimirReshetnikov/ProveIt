# Scaled-base conditional Pell growth

`Direct80ScaledGrowth.power_bound_scaled` generalizes the existing power bound to independent nonnegative model elements `S` and `Y`. Under `X≥16`, `S≥1`, `r≥2`, `c=kY+eta`, `k=eta+zeta`, `zeta>0`, and the exact ordinate equations `c=ycoord (2r+1) (S*(X+1))` and `k=2*ycoord (r+1) (2*(X*S*S−1)+1)`, it proves `2^(2r+1)<Y` in every indicated IΣ₁ model. It reuses the existing Pell recurrence comparison, while keeping the smaller remainder scale `Y` in the final bound.

**The current 80-row graph has main Pell parameter `S*(X+1)−1`, not `S*(X+1)`.** Consequently this checked abstract lemma does not by itself apply to that graph. A [corrected scaled bound](MINUS.md) has since been checked for the actual parameter; graph-specific index alignment and its other size hypotheses remain separate work. No graph-to-halt or iPRA conclusion is claimed.

The selected-provider guarded author run `run.py`, `observations/growth-attempt01/`, passed in session 1788 with exit 0; it records the exact source, object, predecessor and resource data. The project union is pinned to the recorded 1,291-object provider; package-transitive, dynamic and historical source/object ancestry are inherited. No independent Lean replay is claimed.
