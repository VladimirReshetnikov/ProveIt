# Independent natural 89 existential-r replacement review

This is a source-level review of the stable
`research/ordinary13-natural89-r-replacement-model-draft/`, including its
separate mixed-bridge composition. It is not a Lean elaboration or provider
replay. The checker pins the source, author receipt, auxiliary interfaces,
and exact prototype graph.

The prototype's first root is
`Z = b*(ell+k+r-k*Bt)-Bt`, where `b=J*beta`, and its first residual is
`Z²-b²*(1+ell*(ell+k))`. The actual graph has
`ell=(X*Y)*(Y*k)=(X*Y*Y)*k=m*k`. The checker proves by integer polynomial
normalization the exact identity
`ell*(ell+k)=m*(m+1)*k²`, and verifies the literal graph rows. In the stated
all-model first-norm hypothesis these are the source helper's required
`b, ell, k, Bt, Z` arguments. The separate proposed helper requires `b>0`
and `k≥2`; the client obtains these from prototype J positivity and compact
beta positivity, and from raising eta before using `k=eta+zeta+1`.
These supporting source proofs and model providers remain unelaborated.

When the input r is zero, the proposed helper extracts the signed-root
alternatives and positive quotient from the first norm; its second helper
excludes the positive alternative and replaces r by `2*tau`, which flips Z and
preserves Z². This is an existential witness replacement, not a claim that
the original r is positive. The receipt verifies that only the first factor
among `A0`, `A1`, `Fa`, `Fs` depends on r, and pins every product row;
therefore preserving the first-root square preserves the entire prototype
output, assuming the displayed factor interfaces and ring identities.

The composed forward maps raise coordinates 0, 12, 6 and 9, all disjoint
from coordinate 8, so they commute with changing r and preserve f=3 and
y=11. The four exact graph-map implications are still proposed source theorems.
The source uses their forward direction to reach the 85 graph and their
reverse *evaluation equivalences* to transport the modified zero back to 89;
it does not need predecessor witnesses or `ForcedEta` for this local r step.

The separate mixed composition combines this proposed `RReplacement` with
the separately proposed `DirectFY`, and keeps the exact positive-shifted 80
`PolynomialBridge` as a premise. Its 85 native client additionally requires
`ForcedEta`. No all-model root extraction, kernel-checked provider, fixed
external port/PDF identification, or end-to-end iPRA endpoint follows from
this review or its receipt.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-natural89-r-replacement-factor-independent/check.py
```
