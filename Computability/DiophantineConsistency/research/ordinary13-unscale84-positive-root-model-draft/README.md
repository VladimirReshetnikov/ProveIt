# Shifted positive root for 84→87 unscaling

This is unelaborated fact-level Lean source. It does not yet bind either
literal graph, extract large-k or norm facts from a graph zero, authenticate
providers, or prove an endpoint.

For positive P=b*t and a natural tau with `ell+s<tau`, the proposed helper
sets `r=k*(P-1)+t+(tau-(ell+s))`. It proves r>0 and the exact signed identity
`b*(ell+k+r+s-k*P)-P=b*tau`. The extra `+s` is essential: it is the shift
between the old scaled and new unscaled first-root expressions. The positive
witness is fresh and does not assume `r84−s>0`.

The second helper uses the existing source-only signed first-root extraction
to obtain P=b*t and the same natural tau from a source root of either sign.
Its strict margin is an explicit universally quantified premise. The final
fact-level specialization proposes to supply that margin from the q³ data and
large-k bound via the separately reviewed but unelaborated
`UnscaleFirstMarginDraft.qcube_margin`. The literal 84 source norm, positive
b, represented ports, Y=q³s and large-k facts still need actual graph clients.

The checker pins the two fact-level dependencies and tests exact q³ Pell
instances and shifted root identities. These finite controls do not prove the
Lean statements or all-model transfer. From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-unscale84-positive-root-model-draft/check.py | cmp - research/ordinary13-unscale84-positive-root-model-draft/receipt.json
```
