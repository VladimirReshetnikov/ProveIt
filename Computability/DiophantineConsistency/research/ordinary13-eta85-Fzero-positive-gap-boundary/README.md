# F-unshift: first-norm witness and the small-k main gap

This source-only packet narrows the open **F=0, C>0** branch of the [84-row F probe](../ordinary13-eta85-shift-boundary-probes/). It does not prove the probe has a zero at the fixed compact tuple or that its zero existence matches the 85-row parent.

For any ordinary positive natural `beta,K0`, and arbitrary natural mask ports, choose

```text
J=1, F=0, alpha=1, w=0, s=1, eta=0, n_zeta=1,
k=2, X=0, B=beta*K0,
r=(2*beta+1)*K0−1.
```

All these coordinates are natural; the actual F-probe first root is `Z=beta`, so its first residual is zero and `C=beta>0`. Thus the first norm alone cannot exclude F=0 in the remaining positive-gap branch, even for the fixed tuple's positive beta and K0. No main norm or full graph zero is asserted for this assignment.

In fact, the **main norm alone** excludes k=1 and k=2 for either the original parent or this F probe at ordinary natural ports with q≥2. Write `Y=q³s` with s≥1, `a=Y*(X+1)`, `A=a+2`, `c=Y*k+eta`, and `k=eta+n_zeta+1`. Then Y≥8, a≥Y, and `0≤eta≤k−1`. For k=1 or 2,

```text
1<c≤2Y+1<2(Y+2)≤2A.
```

The main signed norm is `Dstar²=U²*(1+(A²−1)c²)` with positive integer `U=Yq²`. Integer square divisibility gives `U | Dstar`, so the radicand would be an integer square. But the following exact identities make it lie strictly between consecutive squares:

```text
1+(A²−1)c² − (A*c−1)² = c*(2A−c) > 0,
(A*c)² − (1+(A²−1)c²) = c²−1 > 0.
```

Consequently a valuation satisfying the main norm has k≥3; extracting that norm from a full product zero is a separate factor-unit step. The explicit F=0 first-norm witness above has k=2, so it cannot satisfy the main norm for **any** choice of its remaining coordinates. The F=0, C>0 branch with k≥3 remains open, as do an existential reverse map and an iPRA proof.

The checker pins both exact graphs and the preceding probe receipt; it verifies the relevant row wiring and the two square-gap polynomial identities, and evaluates bounded actual positive-port instances of the first-norm family. Finite controls do not replace the quantified arithmetic proof. No Lean, build, provider or model interpretation was performed.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-eta85-Fzero-positive-gap-boundary/check.py | cmp - research/ordinary13-eta85-Fzero-positive-gap-boundary/receipt.json
```
