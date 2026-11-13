# Conditional IΣ₁ model transfer for the 38-variable quartic

This is an inert source-only Lean proposal for the corrected
[38-variable quartic](../adaptive-square-sums38-two-quadratic-products/candidate.json).
It is based on the historical **positive 40-variable** expression
`AdaptiveQM40Context.literal CurrentWindowCarry2011.ports` and the author-side
`IPRAQM40Native` endpoint. It is not a direct reduction of the separate
natural-79 compact-port graph. No Lean command, axiom report or staging has run
for this packet, and no new unconditional iPRA endpoint is claimed.

`AdaptiveQM38Literal.lean.src` transcribes all 160 positive-domain arithmetic
rows and the 38 ordered inputs from the corrected candidate. The two removed
40-variable coordinates are zero-based slots 29 (`ellProductVariable`) and
33 (`deltaProductVariable`). `project` drops them; `extend` restores, from the
38 remaining coordinates,

```text
slot 29 = ell * (ell + (eta + zeta))
slot 33 = delta * cSquare.
```

The proposed positivity lemmas use positivity of the original 38 inputs; the
restored products are positive. `AdaptiveQM38ParentSlots.lean.src` proposes
to derive the two slot equalities from residuals 20 and 24 of the parent
sum-of-squares, via `AdaptiveQM40Zeros.new_all` and the natural-model
difference-ring embedding. Those declarations remain unelaborated; no truth
of the parent zero or positivity is assumed outside their stated hypotheses.

The exact missing model obligations are explicit in
`ZeroPreservationObligations`: in **every** model satisfying the repository's
IΣ₁ assumptions, a positive parent zero projects to a child zero, and a
positive child zero lifts to a parent zero. Given those hypotheses, the
proposed client uses the repository's positive-shift argument to transfer
`SameNoZero`, then `HAExpressionNoZeroEquiv.bridge` and the parent bridge to
obtain conditional native, standard and equality-only reference iPRA
biconditionals. Every proposed endpoint still takes the obligations as a
parameter; no standard-natural observation is substituted for a model proof.

`AdaptiveQM38EvaluationCut.lean.src` proposes reducing **both** zero-map
obligations to the single still-unproved statement that, for every such model
and every 38-vector, parent evaluation at `extend v` equals child evaluation
at `v` in the model's difference ring. The reverse direction also uses the
proposed parent slot lemmas and `extend (project v) = v` when those slots have
their defining values. A formal proof of that ring identity should compare
the 29 retained residuals, show the two removed squared residuals vanish, and
preserve every sum edge, particularly `add_scaledIndex = add_product2 +
scaledIndexConstraint`. The author candidate's exact external residual checks
are evidence for this approach, not a Lean model theorem.

The read-only checker pins the corrected 38 graph, the historical 40 graph and
source, and these draft files. It verifies the full parent and child source
schedules, the exact six removed and four changed rows, residual indices,
coordinate order, and 100 finite modular forward controls. Those controls
are not a universal evaluation identity, do not show the Lean scripts compile,
and do not establish the quartic's model equivalence. The author's separate
candidate checker provides external exact residual and quartic-degree checks.
The natural-shift graph has a separately reported operation count and the
historical 40 endpoint retains its own provider and axiom boundaries. No
TeX/PDF association is made here.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/adaptive-qm38-conditional-model-draft/check_source.py | cmp - Computability/DiophantineConsistency/research/adaptive-qm38-conditional-model-draft/result.json
```

`generate_literal.py` regenerates only the literal in this packet from the
pinned corrected candidate; it does not run Lean.
