# Uncompiled concrete reference and extraction direction

`Norm38Reference.lean` drafts the source-specific continuation of the
separately drafted 29-slot extraction. It defines an 81-node ring reference:
14 shifted inputs, four ports, constants 1/3/4, then the first 60 source graph
rows. It proposes proofs that the actual static gate list is topological, that
the reference satisfies each gate, and that its six relevant nodes equal the
`Carrier65.core` fields P, Q, U, W, Z and delta.

With `gatesHold`, the separately drafted generic topology theorem and fixed
point theorem should identify the static nodes with that reference. With
`fiveNorms`, P=Q=U=W=1 and Z=delta then imply `Carrier65.value=0` directly by
the definition of value. This extraction direction needs **no delta
cancellation or positivity**. The final proposed theorem composes this with
`Norm38SlotExtraction.seed_zero_static` and the existing source evaluator to
obtain a 14-coordinate `expressionAt p` zero from a seed zero. It explicitly
requires a model of IΣ₁ and, for all four indices, equality between the cast
integer port `p` and its model-natural representative. The 14 output inputs
are the first 14 witnesses, shifted by one.

**Every Lean declaration in this packet is uncompiled.** The imported generic
topology draft and slot-extraction draft also remain uncompiled. In particular,
`decide` on the finite topology, reduction of the 81-node vectors, the large
`simp`/`ring` computations, proof elaboration and the imported
`FreshModel106` provider route may need repair or separate resource-bounded
checks. The result is a proposed **one-way** extraction, not an equivalence or
iPRA endpoint.

`generate.py` pins the original graph and emits the exact 60 reference rows.
`check.py` independently compares each row and initial node to that graph,
checks the ordered DAG property and terminal indices, and reuses the prior
external source-DAG parser to compare N0/P, N1/Q, Na/U, Nt/W, scaled_Ns/Z and
Delta/delta modulo its documented associative/commutative normalization.
This is an external source check, not Lean parsing or proof validation. Run
`python3 -I -S -B check.py`; no Lean process is used.

Fixed-current-port model-cast lemmas, the reverse witness construction, any
necessary positive-delta argument in that reverse direction, Jones composition
and iPRA transfer remain separate work.
