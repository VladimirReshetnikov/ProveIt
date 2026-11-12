# Independent review: eta-natural Pell growth

The revised source draft's hypotheses match the pinned `power_bound`
interface and its subsequent direct projection client. The first and main
indices, main root, and two different w witnesses are consistently identified
at the statement level. No mathematical mismatch was found in the displayed
bound reduction. This is source inspection and bounded checking, not Lean
elaboration, graph extraction, provider verification, or an iPRA proof.

Given `q≥16`, positive `w0`, and `X=q*w0`, the source gets `X≥16`.
Given positive `s` and `Y=q³*s`, it gets `Y≥1`. It takes the **same** n in
`2*n=R+1`, `n≥13`, and the first ordinate equation. The natural predecessor
`r=n−1` is justified using `n≥1`, and the revised code derives `r+1=n`,
`r≥2`, and `R=2*r+1` by explicit ordered-model addition and cancellation.
This matches the corresponding predecessor argument in the pinned
`ArithmeticAdaptivePowerGrowth2011.growth_of_facts` source. An earlier
version used `omega` directly on the abstract model type V; the reviewed
revision removes those two tactic calls. The revision itself has not been
elaborated.

The remaining `power_bound` assumptions match literally: `c=k*Y+eta`,
`k=eta+zeta`, `zeta>0`, the main ordinate at `R`, and the first ordinate at
`n=r+1`. No positivity of eta is assumed. The returned bound has the
correct exponent after rewriting `R=2*r+1`. The prototype rows use
`X=q*n_w`, `Y=q³*(n_s+1)`, and `k=eta+(n_zeta+1)`; proving those
representations and `n_w>0` at an actual graph zero remains separate.

The subsequent `power` theorem passes the same `main` through both main Pell
coordinates and the no-`E*q` oriented balance, and supplies the separately
assumed exact quotient `w` in the latter theorem's expected slot. Its `w0`
is the graph X-input and is not conflated with that quotient. It also retains
all hypotheses of the direct projection draft, including positivity and the
exact carrier. The fixed compact-port bound `q≥16`, graph-factor and natural
norm extraction, index witness construction, compatible providers, and all
zero-map/iPRA work are not established here.

The independent receipt pins the revised source, its README, the prototype,
the direct projection draft, and the two relevant model sources. It checks
exact theorem signatures and runs 1,000 predecessor/index controls and 500
positive-parameter coefficient controls, including eta zero. The controls do
not certify the model theorem or Lean tactics.

From this directory run

```
python3 -I -S -B check.py > /tmp/eta-zero-growth-independent.json
cmp result.json /tmp/eta-zero-growth-independent.json
```
