# Proposed named-33 natural-164 Lean evaluation bridge

This packet contains inert source for the exact [33-variable, 164-operation
natural-domain graph](../adaptive-named33-natural164-signed-cancel/README.md),
and proposes an all-port ring-evaluation bridge to `positiveShift` of the
historically matched `AdaptiveNamedValues33.literal`. These are current-2011
ports, not the separate natural-79 compact-port equation. Every `.lean.src`
declaration, tactic, `rfl` step and `#print axioms` remains **unelaborated**.

The generated literal transcribes all 164 source rows; two generated residual
vectors expose the same 20 squared residuals in the original 139-row parent
and the new graph. Their ordered-sum-to-literal declarations propose `rfl`.
The generator checks those ordered sums externally as exact DAGs; this is not
Lean reduction.

The bridge proposes each of the 20 residual evaluations independently, using
four instances of `(a+1)-(b+1)=a-b` at the signed pairs for `namedBt`, `Z`,
`Dstar`, and `V`. It combines the residual equalities with the existing
`ModelJonesSyntax.evalRing_subst` theorem to propose equality of the complete
outputs for arbitrary integer ports and valuations in every commutative ring.
`EvaluationIdentity` states that full universal condition explicitly. The
native, standard and equality-only reference iPRA clients take it as a
hypothesis and reuse `IPRANamedValues33Native.bridge33`; the proposed proof of
the hypothesis is itself untested.

The read-only source checker pins the 139-row parent source, 164-row candidate,
matched parent endpoint and generated drafts. It independently interns the
shifted parent and child expression DAGs and checks all 139 parent row terms
after exactly the four permitted cancellations. It also checks the 20 residual
mapping declarations and explicit conditional endpoint. The author's external
DAG/degree checker and both source receipts reproduce. None parses or runs
Lean, authenticates full provider ancestry, reports axioms, proves a new iPRA
derivation, or establishes physical TeX/PDF semantics. The historical
matched native replay retains its stated inherited project, package and
dynamic-dependency limits.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/adaptive-named33-natural164-lean-bridge-draft/check_source.py | cmp - Computability/DiophantineConsistency/research/adaptive-named33-natural164-lean-bridge-draft/source-result.json
```

`generate.py` regenerates only this packet's inert source and observation; it
does not invoke Lean or create a build tree.
