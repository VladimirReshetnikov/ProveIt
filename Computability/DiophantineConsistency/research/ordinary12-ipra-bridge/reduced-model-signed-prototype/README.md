# Signed model fraction integrality

`ReducedNormSigned.signed_denominator_divides` proves the unbounded signed
integrality lemma in the difference ring of an arbitrary `IΣ₁` model. Its
inputs are a **model natural** `r>0` and arbitrary **signed difference-ring**
elements `z,y,d`, with

```
d ≠ 0,
(ιr+1) z² d² = ιr y² + d².
```

Here `ι` is the canonical embedding of the model naturals in its difference
ring. The conclusion is `d | y` **in that difference ring**. The theorem
does not require signs of `z,y,d`, a gcd or Bézout certificate as an input,
the actual graph, or the desired strong norm.

The proof uses `nonneg_or_nonpos` to select natural magnitudes for each
signed coordinate, retaining its sign and proving the square identity.
The nonzero signed denominator forces its natural magnitude to be positive.
Injectivity of `ι` transports the cleared equation to the model-natural
norm; the independently audited [natural normalization theorem](../reduced-model-normalization-prototype/README.md)
then supplies divisibility of natural magnitudes. The four numerator and
denominator sign combinations yield the stated signed divisibility.

This is a model theorem, not a Lean proof object showing that its
counterpart is provable in iPRA. The actual graph's coefficient must still
be bound to `ιr+1` for a **positive model natural** `r`, and its proved
nonzero denominator and cleared equation must be passed to this lemma.
Deriving the ordinary strong norm and a proof-producing object-theory bridge
are also separate obligations.

## Paired evidence

The [replay](replay.py) pins the independently audited natural-normalization
parent, matching seed objects, prior reduced-norm/current-provider chain,
and the reviewed sampled monitor. It builds the source separately on the
author and peer sides, checks exact direct imports, and compares objects,
axiom reports and parent states. The sampled RSS/free-space stops are not
hard quotas or whole-process-tree guarantees; package-transitive, dynamic,
Foundation outer-wrapper and process-group caveats remain inherited.

Actual wrapper session `62334` exited `0`, printing receipt SHA
`576041dbd94d2aaa76a63ab4515164e6b783d106f9d92a3891c260c88eb8b30a`.
The [receipt](evidence/receipt.json) records compiler and dependency-check
exits `0` for both sides and matching object hashes and reports. The
[author](evidence/author.log) and [peer](evidence/peer.log) logs contain no
warnings or `sorryAx`; their reports list only `propext`,
`Classical.choice`, and `Quot.sound`. This new packet still needs an
independent review.

The retained [failed attempt](observations/attempt01-terminal.json) was
session `21831`, actual exit `1`, because a rewrite did not match a
left-associated multiplication. Its source is preserved and its failed
report included `sorryAx`. Exploratory session `53995` then exited `0`;
the paired replay above is the evidence for the present source.

When the pinned temporary providers remain available, and after coordinating
other Lean processes, reproduce with

```
python3 -I -S replay.py --output /tmp/ipra-reduced-model-signed-new
```
