# A positive strictly smaller transformed coordinate

This packet continues the independently quantified reduced-norm descent
inside arbitrary `IΣ₁` models. It does not assume the 12-variable graph,
its strong norm, a final rank, or any iPRA derivation.

Over an ordered commutative ring, `ring_transform_v_ne_zero` assumes
`r>0`, `b>0`, the reduced norm

```
(r+1)(vb)² = r a² + b²,
```

and an already supplied square-divisor witness `r=b²s`. Using the previous
cleared norm-preservation identity, it proves

```
v′ = (2r+1)v − 2bsa ≠ 0.
```

Unlike the strict-decrease result, this generic nonzero theorem does not
assume `v>1` or a Bézout certificate. The positive `b²` term rules out a
zero transformed first coordinate.

`model_smaller_first` combines nonzero with the preceding packet's actual
square-divisor witness and strict interval. In an arbitrary `IΣ₁` model,
assume `r>0`, `v>1`, `b>0`, `Bez a b 1` and the displayed reduced norm.
It constructs natural model elements `s,k` such that

```
r=b²s,  0<k<v,  ιk=v′ or ιk=−v′.
```

Thus `k` is the positive absolute value of the transformed signed first
coordinate and is strictly smaller than `v`. Both signs are retained
explicitly; the statement does not silently discard a sign or assert
standard-natural well-foundedness for a nonstandard model.

The previous packet separately supplies a natural transformed numerator
and its Bézout certificate, but these existential witnesses are **not yet**
assembled here into a single new natural state with the reduced norm. That
simultaneous state transport, least-number/primitive-recursive iteration,
model rational normalization, graph binding, and internal iPRA proof remain
open. In particular, neither this packet nor the previous one proves the
unbounded integrality claim.

## Paired current-provider evidence

The [replay](replay.py) builds this source separately over the two matched
current-provider overlays of the [reduced-norm descent-step packet](../reduced-model-descent-prototype/README.md),
checking its source/seed receipt, underlying square-divisor parents, the
70-source provider comparison and exact direct imports. The audited sampled
monitor is reused. It does not impose hard total-process-tree resource
quotas or establish package-transitive/dynamic ancestry.

Actual wrapper session `88085` exited `0` and printed receipt SHA
`01af03ae511a9a94c65fb60d1d2a634dc1b502e18bcd6a9584296bdb2d14bedb`.
The [receipt](evidence/receipt.json) records both compiler and dependency
check exits as `0`, matching sibling objects and axiom reports, and sampled
peak RSS. Both [author](evidence/author.log) and [peer](evidence/peer.log)
logs are retained. The two reports use only `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorryAx` or warnings. The immediate parent is a
paired model suffix whose independent review was pending at the time of this
run and has since [passed](../../../reviews/ordinary12-reduced-model-descent-independent-audit/README.md),
with a documented historical README-only drift qualification. This new
packet also needs independent review. No iPRA conclusion is claimed.

The [observations](observations/) retain two earlier source files and actual
exit-1 records: the first introduced a `let` rather than a zero equation,
and the second needed conversion between square notation and multiplication.
Exploratory session `63210` exited `0` for generic nonzero, and session
`55676` exited `0` for the combined model measure; the paired run above is
the reproducible evidence for the current source.

When the pinned temporary providers and suffix parents remain available,
and after coordinating other Lean processes, reproduce with

```
python3 -I -S replay.py --output /tmp/ipra-reduced-model-nonzero-new
```
