# Independent review: symbolic model iff, port projection and finite row transfer

These are distinct results: the symbolic model equivalence uses the compact symbolic kernel parameter; the finite row transfer concerns direct-BFS and original Lean tables. This review does not conflate those parameter choices or claim a completed model-level transfer between the two results. The three `check-*.py` scripts validate accepted author receipt/source/runner/copy/object/log hashes, pre/post input pins, and first resolution of all eight distinct source-direct import occurrences. They scan accepted sources for `sorry`/`admit` and logs for diagnostics/`sorryAx`; exact selected paths, hashes, axiom reports and receipt hashes are in the corresponding output files. No Lean replay was performed; transitive selection, source-object, package and dynamic-library provenance remain inherited.

## Symbolic model equivalence

`Direct80SymbolicModelIff.symbolic_positive_model_iff` works in an arbitrary model of `IΣ₁`. For a natural `p : Fin 4 → ℕ`, it assumes `p 0=betaNat`, `p 2=lowNat`, `p 3=betaNat+highNat`, the full integer tuple equality `integerPorts p=CompactSymbolicModelIff.p`, and the **model** equality `(p 1:V)=paramKernel rho`. Under these assumptions it concludes

```text
(∃ v : Fin 10 → V, (∀j,0<v j) ∧ InternalZero (graph (integerPorts p)).output v)
  ↔ (∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0).
```

The forward theorem uses the full symbolic tuple equality; the reverse uses the model port equations. The proof derives the beta and mask model casts from the given natural equalities and selected beta/mask cast theorems. The matching direct providers include the separately reviewed halt-to-graph object and the previously checked graph-to-halt object. Accepted `iff-attempt04` object SHA `938e75e9120099512d87aebebb847c60d6aa06d6820eef5b7ce4f46110345fe7`; its axiom report is `[propext, Classical.choice, Quot.sound]`.

`Direct80SymbolicPortProjection.symbolic_iff_of_four_ports` removes the extra tuple and model-cast hypotheses **when** the four natural coordinate equalities are given:

```text
p 0=betaNat        p 1=paramKernel rho
p 2=lowNat         p 3=betaNat+highNat.
```

Its generic four-coordinate extensionality lemma establishes `p=ports beta kernel lo hi`; the proof obtains integer tuple equality by congruence and the model-cast equality by congruence. It does not need to expand the huge kernel. The projection directly selects the same accepted iff object above, SHA `938e…45fe7`; its accepted `projection-attempt01` object SHA is `b29a920b26eaa4ee347d9471a4a32bf38785883719826ceaa3246f37b4ae8809`, and both printed projection declarations report `[propext, Classical.choice, Quot.sound]`.

Both implications are **model** statements about possibly nonstandard T and InternalZero. They do not show a standard machine halt, prove existence of a syntactic iPRA proof, or identify the symbolic `paramKernel rho` with the different K0 in the retained 80 JSON/PDF. The four natural equalities are still theorem premises, not established file-binding facts.

## Standard finite row transfer

`DirectBFSRowTransfer` identifies in-bound `getD` lookups with the typed original and direct Lean list rows, and proves for each `j : Fin 943`

```text
rowForward (rowBackward j) = j
rename (Compact943Data.row (rowBackward j)) = DirectBFSSymbolicKernel.row j.
```

Thus `rowBackward` selects an **original** row for a direct row j, and `rename` maps its horizontal/vertical original colors **to direct colors**. The theorem has no arbitrary-model word, edge-adjacency or machine-run quantification. Its selected `DirectBFSConjugacyLift` object hash `4ff48994bfef89bf7bce5e1473a261dd7eb19e07fd579cd7658dede08716c39e` matches the independently reviewed lift; the selected original table object SHA `9ed9ec865af1b8b3794328655ca7cb9161cb8573460c82f80c5db8c35db4bf7b` matches the finite sweep by bytes even where selected paths differ. Accepted attempt02 object SHA `b9e58f3133aa17b154f1e875d2d0304c30fd0d97dc56b96576bfd6b6f1f58fda`; `original_row` and `direct_row` report `[propext]`, the other two report `[propext, Quot.sound]`. Attempt01 exited 1 with lookup elaboration errors; it is not accepted evidence.
