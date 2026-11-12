# 75↔74 positive-zero model comparison — source draft

This source-only wrapper composes the 75→74 positive witness map with the
74 own-zero strict guard bound and the conditional reverse map. It explicitly
requires difference-ring discreteness, positive model beta, and beta/K port
casts; K is a natural model element, corresponding to the external K≥0
condition. The natural-port specialization uses `P72Root.cast_port` at slots
0 and 1. Each direction starts from its own graph zero.

Discreteness is deliberately a premise; a future specialization may use
`ModelArithmetic.model_discrete`, subject to its separately audited provider
and unelaborated imports. All maps, factor clients and this source remain
unelaborated. This is not a verified model/halting bridge, iPRA endpoint,
provider proof or physical byte/PDF binding; no Lean run occurred.

Independent source review: [75/74 model wrapper](../../reviews/ordinary14-75-74-model-equivalence-independent/README.md).
