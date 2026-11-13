# Independent source review: conditional QM38 model transfer

The [conditional model draft](../../research/adaptive-qm38-conditional-model-draft/README.md),
its checker and this independent source/interface checker reproduce. The
reviewed coordinate maps, parent residual indices and directions of the
proposed evaluation-cut reduction are consistent at source level. This is not
Lean elaboration or a proof of any of the stated model obligations.

The child literal matches the corrected 38-input, 160-row candidate exactly.
Relative to the parent 40-vector, `project` drops zero-based slots 29 and 33;
exhaustive index checks verify its retained coordinates and the inverse index
mapping in `extend`. The five unshifted coordinates used in the inserted
products are `ell=17`, `eta=9`, `zeta=10`, `delta=26`, and `cSquare=22` in both
vectors. Thus the proposed extension restores slot 29 as
`ell*(ell+(eta+zeta))` and slot 33 as `delta*cSquare`. Positive child inputs
make both inserted products positive. `extend (project v) = v` is asserted
only after those two slot equalities hold.

The parent source's ordered residual list has `ellProductDifference` at index
20 and `deltaProductDifference` at index 24. `AdaptiveQM40Zeros.new_all`
claims that a parent zero makes every residual zero; the proposed parent-slot
lemmas use those two indices, `internalZero_iff`, and the injective embedding
to recover exactly the required slot equalities. Their `change`, cast and
simplifier steps have not been checked by Lean here.

The conditional `ZeroPreservationObligations` explicitly quantifies over every
repository IΣ₁ model: positive parent zeros must project to child zeros, and
positive child zeros must lift to parent zeros. Only assuming both does the
client propose the positive-shift no-zero comparison and native, standard and
reference iPRA biconditionals. The model assumptions and the positivity of the
original vectors are explicit. The parent is the positive 40-variable graph at
`CurrentWindowCarry2011.ports`, not the separate natural-79 compact-port graph.

`EvaluationCut` is a stronger, still-unproved premise: for every such model
and **every** child vector, parent evaluation at its extension equals child
evaluation in the model difference ring. Its proposed client uses the parent
slot equalities to rewrite a parent zero as an extended projected tuple; then
it applies the cut in the reverse direction to obtain a child zero. For a child
zero it applies the same cut forward to obtain a parent zero. The two directions
are correct at the stated source-interface level. The independent external
quartic review already checks the corresponding formal polynomial residual
identities, but that is not a Lean proof of this all-model equality.

The shift/no-zero and reference-conversion tactics, parent-slot proofs,
evaluation cut, compatible providers and axiom closure remain unverified. No
unconditional QM38 endpoint, physical file binding or ZFC consistency proof
follows from this packet.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/adaptive-qm38-conditional-model-draft/check_source.py | cmp - Computability/DiophantineConsistency/research/adaptive-qm38-conditional-model-draft/result.json
python3 -I -S -B Computability/DiophantineConsistency/reviews/adaptive-qm38-conditional-model-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/adaptive-qm38-conditional-model-independent/result.json
```
