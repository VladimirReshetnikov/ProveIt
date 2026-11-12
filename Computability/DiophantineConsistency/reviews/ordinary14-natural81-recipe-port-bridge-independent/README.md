# Independent source review: natural-81 recipe-port client

The [client draft](../../research/ordinary14-natural81-recipe-port-bridge-draft/README.md) proposes the expected rewrite from the symbolic natural-81 graph to the graph at `CompactBytePortsModelIff.byteP`, followed by the polynomial bridge and three iPRA endpoint clients. The symbolic and recipe-port definitions use the same `P81NaturalForcedJ.graph` with different port tuples. The source `byteP_eq` states equality of the decoded closed Lean byte-list tuple and the symbolic tuple. Both receipts reproduce; neither runs Lean.

The independent checker parses the client imports and confirms its two bare draft modules and 11 explicitly imported qualified project sources against pinned source bytes. It checks the graph references, the proposed `byteP_eq` rewrite, four endpoint target statements against the corresponding symbolic endpoint declarations, and the five `#print axioms` commands. The source explicitly opens `HAExpressionAssembly` for `PolynomialBridge`. This is a bounded direct-source and signature comparison, not actual Lean module resolution, type checking, or proof that all transitive providers and instances are available.

All five axiom-report commands remain unexecuted. The proposed rewrites, natural-81 endpoint chain, provider and axiom closure, and iPRA derivability remain unverified. Closed Lean lists are not by themselves a theorem about external P72/P115 files, the candidate JSON or its operation count, or the distinct Carrier65 equation displayed in `equation.pdf`; those bindings require separate evidence and, where desired, formal theorems.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural81-recipe-port-bridge-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural81-recipe-port-bridge-independent/result.json
```
