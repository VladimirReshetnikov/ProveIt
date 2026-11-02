# Signed integrality for the free-J ordinary tail

`FreeJGraphIntegrality.graph_denominator_divides` instantiates the signed
model integrality theorem at the **exact 95-operation free-J graph**. In any
`IΣ₁` model, assume natural ports `p` satisfy `0<p₀`, `p₂<p₀`, `p₃<2p₀`,
all twelve coordinates are positive, and the literal graph has an internal
zero. These are conditional model hypotheses; this packet does not establish
the compact44 port interpretation or checker calibration.

Evaluate the actual graph expressions `q,d,z,n` selected by
`FreeJOrdinaryTransport.parts` in the model's difference ring. Put

```
w=n+z, h=(1−q)w²+qz²−1, b=2(1−q)w,
A=dh+q(1−q), D=db, Y=wD−A.
```

The theorem proves `D | Y` **in that difference ring**. These are
proof-only abbreviations; there is no literal denominator gate or added
quantified coordinate. `graphQ_eval` first identifies the actual graph
coefficient `q` with the embedding of the natural model value `Q`; positivity
of the graph input `t` yields `Q>1`, so `r=Q−1` is a positive model natural
and `q=ιr+1`. The independently audited graph composition supplies `D≠0`
and the cleared auxiliary norm. The separately audited signed integrality
theorem then gives `D | Y` for these actual graph expressions.

This is an unbounded **model-level** divisibility statement, not yet the
ordinary strong norm, a compact44 checker calibration, or a Lean proof that
iPRA proves the equivalence. In particular, deriving a signed multiplier,
a positive natural ordinary multiplier, its required norm and subsequent
rank recovery are separate steps. No strong norm is assumed here.

## Paired current-provider join

The [replay](replay.py) joins two separately audited suffixes built over the
same matched 70-source provider: the graph's nonzero-denominator cleared
norm, and signed reduced-norm integrality. It checks every graph suffix
source/object/log row against its receipt and checks the seven joined
integrality seed objects against their own paired receipts. It overlays only
those current-provider suffix objects, rejects collisions, checks exact
direct imports and matched outputs, and compares the 70-source parent before
and after. It does not independently rebuild the two parent chains here.
The graph parent's manifest-at-read qualification and the inherited
Foundation outer-wrapper, package-transitive, dynamic loading, sampled
resource and process-group limitations remain.

Actual wrapper session `87494` exited `0` and printed receipt SHA
`61b12fb93bc50e43ee710b3bac6a1d40cb61f1af1a6fbe3f9861985a06d3dc9d`.
The [receipt](evidence/receipt.json) records the two compiler and import-check
exits as `0`, exact joined seed hashes, matching objects and axiom reports,
and sampled RSS. The [author](evidence/author.log) and
[peer](evidence/peer.log) logs report only `propext`, `Classical.choice`,
and `Quot.sound`, with no warnings or `sorryAx`. Exploratory session `72534`
previously exited `0`. The paired join still needs independent review.

When the pinned temporary parent and suffix artifacts remain available, and
after coordinating other Lean processes, reproduce with

```
python3 -I -S replay.py --output /tmp/ipra-freej-graph-integrality-new
```
