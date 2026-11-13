# Explicit discreteness repair for the first-rank draft

This isolated alternative preserves the pinned `ordinary13-independent-k-first-rank-model-draft` and addresses the specific C-positive discreteness hazard found in `reviews/ordinary13-independent-k-first-rank-source-independent/`. It reflects `F+alpha<q` from the difference ring to model naturals using `ι_lt_ι.mp`, applies the natural successor step `add_one_le_iff.mpr`, then re-embeds it using `ι_le_ι.mpr`. The subsequent signed-ring `linarith` receives the explicit unit-gap inequality.

The source differs from the original by exactly this replacement and the separate namespace/axiom-query names. The conditional main helper call and all model-natural, graph and port assumptions are unchanged. The reproducible checker pins both versions and the independent review and enforces that exact source delta.

**No Lean elaboration has been performed.** In particular the reflection and cast steps, imports, nonlinear tactics and transitive providers remain proposed. This is not an arbitrary-model proof, graph binding, unit extraction, parent-child zero map or iPRA endpoint; `#print axioms` commands are future requests, not results.

Run from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-independent-k-first-rank-discrete-repair/check.py | cmp - research/ordinary13-independent-k-first-rank-discrete-repair/receipt.json
```
