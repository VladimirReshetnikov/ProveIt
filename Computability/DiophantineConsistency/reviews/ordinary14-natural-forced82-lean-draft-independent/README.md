# Independent review: natural-82 Lean graph draft

The [source draft](../../research/ordinary14-natural-forced82-lean-draft/README.md) accurately transcribes the pinned [82-operation candidate JSON](../../research/ordinary14-root74-natural-forced82/candidate.json) at the source-text level. The original source check reproduces its receipt. The separate check here constructs the entire expected Lean file byte for byte from the pinned graph, the declared variable and port order, and a fixed source template, then compares it with the draft. It also checks topological references, liveness of all 82 rows and all inputs and ports, the ten field selections, and the node structure corresponding to the stated output product.

The draft uses the same style of `Expr (Fin ...)` variable and port constructors and arithmetic notation visible in its imported `AdaptiveEquationSyntax2011` source. These observations are not a Lean parse, elaboration, semantic evaluation, provider or axiom check. In particular, the source text of `output_shape` and its `by rfl` proof have not been checked by Lean. The type `Expr (Fin 14)` and the graph source alone do not establish the natural-domain zero argument, its transfer to the positive graph, an iPRA theorem, or physical port/PDF binding. This review does not independently reprove the external zero-existence or degree certificates.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural-forced82-lean-draft-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural-forced82-lean-draft-independent/result.json
```
