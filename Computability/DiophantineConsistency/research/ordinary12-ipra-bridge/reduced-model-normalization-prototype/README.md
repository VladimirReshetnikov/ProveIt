# Natural numerator/denominator normalization

`ReducedNormNormalization.denominator_divides` removes the supplied gcd and
Bézout assumptions from the preceding reduced-denominator theorem. In any
`IΣ₁` model, for model naturals `r,v,y,d`, its exact hypotheses are

```
r>0,  d>0,
(r+1)(vd)² = r y² + d².
```

Its conclusion is the **model divisibility statement** `d | y`. There is no
assumption that the original numerator and denominator are coprime, no graph
assumption, and no use of the desired strong norm.

The proof obtains the existing model gcd certificate for `y,d`, writes
`y=g a` and `d=g b`, and derives `g>0`, `b>0` from `d>0`. It cancels `g`
from the certificate to construct the required four-natural Bézout
certificate for `a,b`, and cancels `g²` from the norm to obtain the reduced
norm. The independently audited [reduced integrality theorem](../reduced-model-induction-prototype/README.md)
then gives `b=1`, from which `d | y` follows. All witnesses and cancellations
are inside the arbitrary model; this is not an argument restricted to
standard naturals.

This theorem covers **nonnegative model coordinates** `v,y,d`; it does not
yet lift signed model difference-ring inputs to their natural magnitudes or
bind the graph's cleared norm to these hypotheses. It does not provide an
object-level iPRA proof or complete the equation/consistency equivalence.

## Paired evidence

The [replay](replay.py) pins the independently audited reduced-denominator
parent, both matched induction seed objects, all prior source-current suffix
seed checks and the underlying matched 70-source provider. It builds this
source separately for author and peer and checks exact direct imports,
axiom reports, source/object hashes and the parent comparison. It uses the
reviewed sampled monitor; RSS and disk limits are not hard quotas or
whole-tree measurements. Inherited package-transitive, dynamic and
Foundation wrapper provenance limitations remain.

Actual wrapper session `54006` exited `0` and printed receipt SHA
`802096243e8d668abecaf1a59e9132a3f21b3db9bdde5f847ba1b97fb113aa65`.
The [receipt](evidence/receipt.json) records both compiler and dependency
check exits as `0`, matching sibling objects and reports, exact imports and
sampled peak RSS. The [author](evidence/author.log) and
[peer](evidence/peer.log) logs report only `propext`, `Classical.choice`,
and `Quot.sound`, with no warnings or `sorryAx`. Exploratory session
`69791` had previously exited `0`; the paired replay is the retained
reproducible evidence. This new packet still needs independent review.

When the pinned temporary provider and suffix artifacts are available, and
after coordinating other Lean processes, reproduce with

```
python3 -I -S replay.py --output /tmp/ipra-reduced-model-normalization-new
```
