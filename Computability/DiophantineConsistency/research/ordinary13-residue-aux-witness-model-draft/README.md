# Residue strong/direct-auxiliary witness conversion draft

This packet proposes the graph-specific witness conversion needed by the
[exact-index client](../ordinary13-residue-exact-index-model-draft/). **No Lean
source, proof tactic, imported object or provider ancestry here has been
elaborated or checked.**

`ordinary_strong` proposes extracting the natural ordinary strong equation
from the actual 90-row graph's strong residual, with the explicit witness
`i'=n_i+1`. `ordinate_pair` relates the graph's signed ordinate to the
natural parts `A=f²*T*c` and `B=f²*R+c`; it requires the explicit `F≤q`
truncated-rank representation premise.

`old_aux_of_direct_graph` proposes turning the actual positive direct y into
a positive old auxiliary witness u with `z+u=y`, then deriving exactly the
natural `absdiff` auxiliary equation required by `P72Exact.indices_ordinary`.
It obtains `1<Q` from the already proposed graph strong/size facts, but it
**retains `1<z²` as a separate explicit hypothesis**. That strict bound,
which may require first/main/strong norm and ordinate estimates, is not
proved here. The represented natural ports, graph norm and f/y forcing,
compact binding, main index, `R≥26`, later Bézout condition and endpoint
remain separate obligations. No eta-zero generalization is assumed.

The source uses the existing source-level `AuxRootModelDraft` order lemmas
and `P72Root.ι_magnitude_sq` to connect the signed ordinate and the natural
`absdiff` squares. Their compatibility and provider provenance require Lean
verification; no old auxiliary coordinate is assumed to be present in the
graph.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-residue-aux-witness-model-draft/check.py | cmp - research/ordinary13-residue-aux-witness-model-draft/receipt.json
```

The read-only checker pins the graph and source interfaces and tests finite
signed auxiliary examples and strong-equation algebra. It never runs Lean,
stages artifacts, or proves the nonstandard-model assertion.
