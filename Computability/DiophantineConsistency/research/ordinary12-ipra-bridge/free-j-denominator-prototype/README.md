# Nonzero candidate denominator from the free-J graph

**Status: bounded Lean replays passed against one shared historical parent;
an [independent bounded replay](../../../reviews/ordinary12-freej-denominator-independent-audit/README.md)
also passed.** Do not interpret this packet as an iPRA proof or as a complete
ordinary-norm recovery.

`FreeJDenominator.denominator_negative` uses the exact hypotheses of
`FreeJGraphVBound.graph_bound`: an arbitrary `IΣ₁` model, natural ports
`β>0`, `MC<β`, `MF<2β` as model inequalities, all twelve coordinates
positive, and an internal zero of the exact 95-operation free-J literal. It
constructs the proof-only graph expressions

```
c = η+Y(η+ζ),     Q = Δ((1+t)²-1),
bₙ = 2(1-Q)(n+V),  D = c⁴bₙ,
```

and proves `(pairEval D).1 < (pairEval D).2`. Hence this signed `D` is
strictly negative, and in particular its pair components are distinct.
`D` and `bₙ` are proof expressions, not new quantified variables; `V` and
`Q` are the exact graph expressions identified in the V-bound packet. The
symbol `d` used inside `Q_eval` is Δ, whereas the original descent plan's
`d` is `c⁴`.

The literal graph has no `bₙ` or `D` gate, so the theorem does not identify a
denominator node in that graph. `graphD` is constructed syntactically as
`c⁴·[2(1−Q)(n+V)]`; source inspection identifies `graphC` with the graph's
`(core p).c`, and the compiled V-bound `shape` theorem pins `graphQ` and
`graphV` to the graph's `QV²−1` subexpression. A separate signed model
bridge must still substitute these exact expressions, including `graphD`,
into the cleared auxiliary identity and prove that its equation follows
from the actual ordinary factor. In particular, the graph's polarized
`core.pa` has `d·h−Q(1−Q)` while the cleared identity's `A` uses
`d·h+Q(1−Q)`. A universal commutative-ring polarization identity relates
the corresponding residuals; its substitution into this graph over signed
model pairs is not established by this packet. A later [signed transport](../free-j-signed-transport-prototype/README.md)
derives the unpolarized norm residual from the graph zero in a difference
ring; its [independent paired replay](../../../reviews/ordinary12-freej-signed-transport-independent-audit/README.md)
passed. A later [coherent composition](../free-j-current-denominator-composition/README.md)
identifies the proof-only denominator and applies the cleared auxiliary
identity. Its paired rebuild passed an [independent artifact audit](../../../reviews/ordinary12-current-denominator-independent-audit/README.md),
with the recorded execution-time manifest qualification. Integrality remains
open.

The proof establishes separately that the signed graph `Q` equals the
nonnegative natural model expression Δ((1+t)²−1) and that this value is
strictly greater than one from `t>0`. The previously compiled `V>c>1`
then implies `n+V>0`. Multiplication of a strictly negative pair by a
strictly positive pair is strictly negative, as is multiplication by the
positive scalar `2c⁴`. No ordinary strong norm, ordinary-tail integrality,
final rank, or checker calibration is assumed.

The inequalities used are necessary for this strict-sign route: `Q=1`,
`n+V=0`, or `c=0` makes the displayed proof denominator zero. These are
edge cases of the algebraic expression, not asserted zeros of the graph.

An exploratory command using Lean 4.32.0, `-M3000 -j1`, and a separate
historical overlay exited **0** with no warnings or `sorryAx`. Its seven
printed axiom reports are `[propext, Classical.choice, Quot.sound]`. The
source SHA-256 is `898b9fa159ba784cc32b71e639a159d785d14e67096aee18a8df07740e23b8a3`;
its immediate V-bound parent object SHA-256 is
`2785949197112d2544646598e6637b29a4dee0fc7d8b41dbca2711febb7e9ec8`.
The exploratory source and dependencies lived under
`/tmp/freej-denominator-overlay`; its historical parent and seed provenance
are described in the [V-bound packet](../free-j-graph-vbound-prototype/README.md).

`replay.py` constructs a fresh bounded overlay from the pinned V-bound
receipt, checks its inherited parent links and object hashes, and records
the direct imports and compiler output. Its Python syntax check exited `0`;
an optimized `python3 -O` invocation exited `1` at the explicit guard
before creating output. Run it only after coordinating with any concurrent
memory-intensive build:

```
python3 replay.py --output /tmp/new-freej-denominator --receipt /tmp/new-freej-denominator.json
```

Two executions used distinct output and receipt paths. The first wrapper
exit was explicitly captured as `0`; the second printed the pass marker,
but its outer exit code was not separately captured by the tool call. Each
[first](replay-01-receipt.json) and [second](replay-02-receipt.json)
receipt records a compiler exit of `0`, a dependency-check exit of `0`,
seven axiom reports without `sorryAx`, and the same generated-object hash
`ede9df1c0bc17b01ad20e5d9717d4425f61f01f70610bb3012f4a8e2ed28b1ca`.
Both executions used **the same** V-bound seed and underlying historical
parent closure. They are repeat runs, not a matched independently rebuilt
provider pair, a source-current rebuild, or a package-transitive audit.

The direct signed graph transport of the cleared auxiliary norm and the
unbounded reduced-denominator descent remain open, as do the compact44 port
binding, object-level iPRA proof, and independent replay. The proof above
therefore removes one model-level prerequisite only.
