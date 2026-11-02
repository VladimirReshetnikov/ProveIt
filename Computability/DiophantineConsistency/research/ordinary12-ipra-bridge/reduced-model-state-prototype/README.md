# A complete smaller reduced-norm state

`smaller_reduced_state` proves a single noncircular descent step in every
`IΣ₁` model. For model naturals `r,v,a,b`, assume

```
r>0,  v>1,  b>0,  Bez a b 1,
(r+1)(vb)² = r a² + b².
```

The theorem constructs model naturals `s,k,t` with

```
r=b²s,  0<k<v,  Bez t b 1,
(r+1)(kb)² = r t²+b².
```

The same witnesses also retain both explicit sign alternatives in the
model's difference ring:

```
v′=(2r+1)v−2bsa,        ιk=v′ or ιk=−v′;
a′=(2r+1)a−2(r+1)vb,   ιt=a′ or ιt=−a′.
```

The proof aligns the two prior square-divisor witnesses by cancellation
using `b>0`; it uses the prior norm-preservation identity, the positive
smaller first coordinate, and the transformed numerator's Bézout
certificate. Squaring the explicit sign cases transports the cleared norm
to the same new natural state. It assumes neither the original equation's
graph nor the desired ordinary strong norm.

This theorem gives the **single descending step**, not a termination proof
or the full unbounded integrality result. A least-number argument must show
its counterexample predicate is `Σ₁` in the formalized model theory; a
separate object-level construction is still needed for iPRA. Gcd
normalization from arbitrary signed graph numerator/denominator and the
graph-specific connection also remain separate.

## Paired evidence

The [replay](replay.py) rebuilds this source separately over both matched
current-provider sides of the [nonzero/measure parent](../reduced-model-nonzero-prototype/README.md),
with the inherited reduced-norm and square-divisor seed checks, exact direct
imports, axiom reports, object hashes and 70-source parent comparison. The
reviewed monitor samples the leader's RSS and host free space; it is not a
hard quota or total-process-tree resource guarantee, and package-transitive,
dynamic, escaped-descendant and PID-race limitations remain inherited.

Actual wrapper session `54636` exited `0` and printed receipt SHA
`81eac0378afbc0b9bfba3d84bfba86d54af1cdc196bf9135391c79778a8002ad`.
The [receipt](evidence/receipt.json) records both compiler and direct-import
check exits `0` and matching source/object hashes and axiom reports. The
[author](evidence/author.log) and [peer](evidence/peer.log) logs report only
`propext`, `Classical.choice`, and `Quot.sound`, with no warnings or
`sorryAx`. The prior model-measure packet has since passed independent
[review](../../../reviews/ordinary12-reduced-model-nonzero-independent-audit/README.md);
this new packet still needs its own independent review.

The [observations](observations/) retain session `74520` (actual exit `0`,
but two style warnings in the less explicit preliminary statement) and
session `40149` (actual exit `1` from redundant tactics in the sign-explicit
version, with `sorryAx` in the failed report). Exploratory session `88955`
then exited `0` without warnings; the paired replay above is the retained
evidence for the current source.

When the pinned provider and suffix artifacts remain available, and after
coordinating other Lean processes, reproduce with

```
python3 -I -S replay.py --output /tmp/ipra-reduced-model-state-new
```
