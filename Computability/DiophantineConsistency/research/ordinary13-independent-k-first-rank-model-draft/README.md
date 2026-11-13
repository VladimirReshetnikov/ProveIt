# First-norm and rank-window model draft

`IndependentKFirstRank.lean.src` is an **unelaborated source-only proposal** for the ordered-model part of the two-norm positive-k argument. Its three declarations draft:

1. A strict model-natural `R+1<q^4` from the signed rank expression, positive beta and J, the two mask bounds, and `G≤q²−2`.
2. The `G≤q²−2` bound from the exact k=0 first norm, including both `C>0` and `C≤0`. In the latter branch the signed first-root equation yields `r=0` and `B=−beta*J`; it uses the explicit positive model-natural `d=X+K0` hypothesis.
3. A conditional composition with the existing `IndependentKZeroMainRankDraft.zero_k_impossible` and its exact main-root, main-norm and `Y=q³s` hypotheses.

Here `q=beta*J+1`, `F` and `alpha` are positive model naturals, and all displayed subtractions in the coefficient and first norm occur in `DiffRing V`. The rank is explicitly required to be represented by a model natural `R`; the source does not silently equate its integer expression to a model value. The source retains `J>0` and `q>0` as explicit assumptions, even though the separate external argument obtains J positivity from the full first graph expression. It requires positive `d`, which would follow from a correctly represented positive compact second port; the kernel and beta/mask casts have not been bound here.

The main helper and this file are drafts, including proposed imports, tactics, instance and cast interfaces. `#print axioms` lines are requests for a future elaboration, not observed output. There has been **no Lean execution, provider selection, proof replay, axiom audit or model-theoretic validation**. In particular, this packet does not extract `A0=A1=0` from the child product, bind the new 84-row graph to these hypotheses, prove `eta≤k`, establish a parent-child zero correspondence, or prove an iPRA endpoint. The prose proof for standard integers and exact graph wiring is pinned separately in `ordinary13-independent-k-two-norm-kpositive-audit`.

An [independent source review](../../reviews/ordinary13-independent-k-first-rank-source-independent/README.md) identified a specific gap in the proposed `C>0` proof: its ring-order `linarith` step needs an explicit model-natural discreteness argument to obtain a unit gap. The reviewed source is preserved as a draft; no successful elaboration of that step is claimed.

From `Computability/DiophantineConsistency`, run:

```sh
python3 -I -S -B research/ordinary13-independent-k-first-rank-model-draft/check.py | cmp - research/ordinary13-independent-k-first-rank-model-draft/receipt.json
```

The checker pins the proposal and relevant inputs and performs bounded lexical/interface checks. It is not a Lean parser, type checker, proof checker or transitive provider audit.
