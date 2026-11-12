# Independent source review: natural-79 literal residue patterns

The [source draft](../../research/ordinary14-natural79-factor-residues-draft/README.md) proposes the intended three literal factor-pattern bindings and a client that supplies the zero-w unit draft's residue premises. The pinned graph's full expression trees match the three inspected generic modulo-four patterns, and the repeated graph let block is byte-identical. This is a source/AST comparison, not a Lean elaboration or a proof of the graph semantics.

The review receipt checks all three proposed `rfl` statement shapes and generic pattern definitions; compares the full symbolic expression trees for the main, auxiliary and strong factors; and checks that the composition calls the three-residue declaration and then the zero-w unit client. The final proposed unit theorem assumes the literal 79 zero and `w=0`, with no additional beta, gamma, J, K0 or residue-premise hypotheses in its displayed signature. Its source dependencies include the separate, still-unelaborated [zero-w unit draft](../../research/ordinary14-natural79-zero-w-unit-draft/README.md) and generic factor-residue draft. Those proposed definitions, proofs, casts and `rfl` reductions still require Lean to check them.

The source checker reproduces and the independent receipt below uses the same pinned graph and generic pattern source but constructs the three expression trees separately. It does not establish model factor units, the later divisibility contradiction, provider or axiom closure, an iPRA endpoint, or a physical-file/PDF binding.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural79-factor-residues-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural79-factor-residues-independent/result.json
```
