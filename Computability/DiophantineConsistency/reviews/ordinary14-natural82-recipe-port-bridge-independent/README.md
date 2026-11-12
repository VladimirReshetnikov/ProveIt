# Independent review: natural-82 closed recipe-port client

The [source client](../../research/ordinary14-natural82-recipe-port-bridge-draft/README.md) proposes the expected rewrite from the symbolic natural-82 expression to the expression at the four closed Lean byte recipes. Its four bridge and endpoint target statements match the corresponding symbolic endpoint statements at the source-text level, using the respective local `expression` definitions. Its `expression_eq` proposes using `CompactBytePortsModelIff.byteP_eq`, and each subsequent client rewrites with that equality. Both source receipts reproduce.

The independent checker pins the natural-82 client and endpoint, the byte-port declaration and its list-decoding dependency, the symbolic-port declaration, and the source of `PolynomialBridge`. It checks the two graph instantiations, `byteP_eq : byteP = p`, all four client target statements and endpoint references, and five `#print axioms` commands. The natural-82 client now explicitly opens `HAExpressionAssembly`, the namespace where `PolynomialBridge` is defined. The separately existing natural-86 recipe client has an unqualified use without that explicit open; its actual Lean name resolution has not been tested here.

These are source and signature observations. No Lean execution checked the rewrite, imports, types, instances, definitional equalities, or axiom reports. In particular, the commands requesting axiom output have not been run. The closed lists and `Nat.ofDigits` statements do not by themselves bind mutable external P72/P115 payload files, the graph JSON, or the distinct displayed Carrier65 PDF. Nor does this client establish its unelaborated predecessor chain or an iPRA derivation. Those obligations are described in the [physical binding audit](../../research/ordinary14-natural82-86-physical-binding-audit/README.md).

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural82-recipe-port-bridge-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural82-recipe-port-bridge-independent/result.json
```
