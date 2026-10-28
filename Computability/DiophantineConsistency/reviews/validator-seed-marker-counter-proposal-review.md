# Marker-counter proposal: scoped mathematical review

27 October 2026. ROOT wrote the proposal, then circuit_reduction read and
challenged its complete argument while the separate guarded-comprehension
compiler ran. No new transport source, cache overlay or compiler was used
for this review.

Reviewed proposal SHA256:
`081cafbc8c3a0044e4aacc9d1b960bc84143d2e98b1d014410ac8a42adee948f`.
Six-source pin JSON SHA256:
`b0880c118fbfe126871ce11f5c7826c7eb280472fdb95e25ff984dd36dcdf110`.

The counter/budget reasoning has no identified mathematical defect. ALL
uses child+(j+1)≤der+j≤B; SHIFT obtains child<j−1 from child<der<j.
The canonical residual sequent satisfies
`R(j+1)={free(¬d(j))} ∪ setShift R(j)`, including the shifted Empty guard.
Generalization and the actual tag-nonempty theorem remove one domain side
formula. At counter0, the actual empty-object witness closes the remaining
universal denial of Empty.

This is a source-plan review, not a Lean validation or full proof-transport
review. The represented family, free/substitution laws, Sigma1 bounded
motive, all ten proof-rule cases and internal discharge induction still
need proofs. Actual tagged and quotient/WF axiom images remain independent
substantial obligations. The existing shift-fixed Good contract is neither
weakened nor applied to a free marker by this proposal.

See the [proposal](../research/validator-seed-marker-counter-proposal.md)
for the exact conditional endpoint, inspected constructor inequalities and
implementation prerequisites. No HA equation equivalence is claimed.
