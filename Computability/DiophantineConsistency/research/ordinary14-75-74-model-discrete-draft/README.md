# Discrete model specialization of 75↔74 — source draft

This source-only client derives the exact difference-ring discreteness premise
of the proposed 75↔74 wrapper from internal model positivity and the existing
`ModelDifferenceRing.one_le_of_pos`. It mirrors the separately existing
`ModelArithmetic.model_discrete` body without importing that larger module.
The resulting wrapper still requires positive model beta and explicit beta/K
casts, or the stated natural-port specialization.

No Lean elaboration or new provider coherence is claimed. The sampled P72 path
lacks the `DiscreteOrderedRingFacts` object, so avoiding `ModelArithmetic` does
not remove all missing provider stages. The graph/model clients remain
unelaborated, and the 78↔75 reverse map, halting/iPRA endpoint, and byte/PDF
binding are not established here.

Independent source review: [75/74 model discreteness](../../reviews/ordinary14-75-74-model-discrete-independent/README.md).
