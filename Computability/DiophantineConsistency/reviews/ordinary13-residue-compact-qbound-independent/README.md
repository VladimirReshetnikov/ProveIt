# Independent review: compact first-port q bound

No concrete source mismatch was found. The local tuple is defined as
`ports betaNat K lowNat highNat = ![betaNat,K,lowNat,betaNat+highNat]`;
its index **0** is beta for every natural K. The actual graph defines
`q=1+v 0*(p 0:V)`, so a positive J=`v 0` and beta≥46 imply q≥47.
The claimed q bound does not depend on choosing a particular K.

`CompactFixedBeta.beta_identity` states in the IΣ₁ model that
`(betaNat:V)+1=Exp.exp ((67:V)*8807)`. The proposed model inequality uses the
existing `ArithmeticStandardCasts.cast_exp` at 6 and the same source pattern
as `CompactGraphDerivedRadix`: `64=Exp.exp 6≤beta+1`, so beta≥46. The
independent check traces a project-source import path from `CompactFixedBeta`
to the cast theorem; it does not authenticate any compiled provider. The
consumer's actual `graph_power` parameters are passed in the correct order,
including positive `p 0`, graph zero, positive J/X, gap, rank window and
q≥46. The cast to integers in the graph expression still has the earlier
source/client proof boundaries; it is not a physical file or PDF binding.

The author receipt and this packet's independent check reproduce. These are
bounded source and natural-number controls, not Lean elaboration, a provider
or axiom audit, a graph bridge, or an internal iPRA endpoint. Run from
`Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-residue-compact-qbound-independent/check.py | cmp - reviews/ordinary13-residue-compact-qbound-independent/result.json
```
