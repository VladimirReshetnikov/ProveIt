# Independent review of fixed compact first index below rank

**PASS within recorded direct-provider scope.** The no-Lean `check.py`
checks the passing attempt02 retained and terminal receipts/logs, source,
runner, helper, output object, all recorded guards, and all three direct
project-provider objects against their successful producer receipts. The
axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`.
This is not a Lean replay; captured transitive, dynamic and between-sample
ancestry remains inherited.

The theorem takes an `IΣ₁` model, an arbitrary natural `K`, and an actual
positive zero of the 72 graph at the fixed symbolic compact tuple
`(betaNat,K,lowNat,betaNat+highNat)`. It concludes that some model first
Pell index `n` is less than the actual graph rank `R`, while also returning
the first Pell coordinate identities. Its composition derives `q≥33` and
the needed positivity and `Y≥2`, extracts `n` from the first residual,
uses the fixed-compact main coordinate at `R`, and applies the generic
first/main index comparison. The index may be nonstandard as an element of
the model.

This does not prove `2n=R+1`, the missing first-index congruence, a 72-to-76
reverse map, a consistency equivalence, or an iPRA endpoint. The source's
“Unchecked draft” header predates the successful attempt02 and is retained
unchanged. The three inputs are reviewed separately in the
[fixed main-rank](../p64-qcube72-fixed-compact-ranked-main-independent/README.md),
[first-index extraction](../p64-qcube72-first-index-extraction-independent/README.md),
and [index comparison](../p64-qcube72-first-index-comparison-independent/README.md)
packets.

Run while captured temporary paths remain available:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube72-fixed-compact-first-index-independent/check.py
```
