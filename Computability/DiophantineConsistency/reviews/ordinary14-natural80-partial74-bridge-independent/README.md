# Independent source review: natural 80 to partially shifted 74

The [bridge draft](../../research/ordinary14-natural80-partial74-bridge-draft/README.md) states the correct changed-valuation relationship for the four pinned literal graphs, and its proposed model equivalence has the correct directions at the related valuations. The original checker and the independent receipt below reproduce. This is a source and external algebra review; none of these source declarations or imported bridge theorems was elaborated in Lean.

The independent checker compares every input and port alias, every literal gate row, the exposed factor/output tuple and the output-product source shape of the Lean drafts with their pinned 80-, 82-, 86- and 74-operation JSON graphs. It verifies the exact two-shift deletion from 82 to 80, the three input shifts and zeta/rank cut connecting 82 to 86, and all shared rows of 86 and 74. Sparse integer-polynomial checks establish the local `qF`, zeta/rank and guard cancellations. These identities plus structural congruence give the external whole-graph equality over arbitrary commutative rings and arbitrary signed ports; finite controls alone are not used for that identity.

The source first subtracts one at slots 0 and 12, then the imported 82-to-86 proposal subtracts one at slots 3, 8 and 11, then the imported 86-to-74 proposal adds one at all slots. The exact composition therefore leaves **J, f, r, y and gamma** unchanged and adds one at the remaining nine coordinates, including h. Since a natural-model embedding preserves zero, one and addition, embedding that partial valuation gives the same ring valuation as partially shifting the embedded coordinates. If the named ring and embedding declarations elaborate, `ModelDifferenceRing.internalZero_iff` supplies both directions of `InternalZero 80 v ↔ InternalZero 74 (partial74 v)`. This is a pointwise statement at a specified related valuation: it does **not** by itself give a zero-existence equivalence with unrestricted 74 valuations, whose nine shifted coordinates would need appropriate predecessors.

The draft has no beta, K0 or coordinate-positivity assumptions for that algebraic comparison. A zero with gamma zero is transported to a 74 valuation with gamma still zero, but the comparison alone does not prove that such a zero cannot exist. It also does not establish the factor-to-main-norm bindings, iPRA derivability, provider/axiom closure, physical coefficient bytes, or PDF semantics. The source's `simp`, `fin_cases`, `rw`, instances and embedding coercions still need an actual Lean check; the two axiom-report commands remain unexecuted.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural80-partial74-bridge-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural80-partial74-bridge-independent/result.json
```
