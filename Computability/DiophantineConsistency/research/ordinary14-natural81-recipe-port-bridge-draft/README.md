# Natural-81 closed recipe-port client: source proposal

`Natural81RecipePorts.lean` is an **unelaborated source-only client** of the
[natural-81 endpoint draft](../ordinary14-natural-forcedj81-ipra-draft/README.md).
It proposes rewriting the 81-operation graph's symbolic port tuple to
`CompactBytePortsModelIff.byteP` using the existing source declaration
`byteP_eq`, then transporting the proposed polynomial bridge and native,
standard, and equality-only iPRA endpoint declarations. It is adapted from
[the independently source-reviewed natural-82 recipe client](../ordinary14-natural82-recipe-port-bridge-draft/README.md),
with the 81 endpoint and graph names substituted and the used project modules
explicitly imported. The source opens `HAExpressionAssembly` explicitly for
`PolynomialBridge`. The five `#print axioms` commands have **not** run and
provide no axiom-closure evidence.

`byteP` decodes closed lists defined in Lean. This client does not establish
that those lists equal external P72/P115 payload files, does not prove that a
JSON graph or its operation count denotes the Lean expression, and does not
bind the result to `equation.pdf`. The PDF currently describes the different
Carrier65 graph and beta, as documented in the [physical binding audit](../ordinary14-natural82-86-physical-binding-audit/README.md).
The 81 graph, strict-K0 argument, endpoint, recipe client, their providers, and
all proposed rewrite and axiom-report steps remain unelaborated and unverified.
No iPRA derivation, physical binding, or global minimality is claimed.

The deterministic source checker pins this client, its natural-82 source
parent, the 81 endpoint and graph, and the 11 explicitly imported qualified
project sources. It compares the complete client text to the 82 client after
specified substitutions and import additions, checks selected declaration
signatures and five requested axiom reports, and does not invoke Lean. It is a
bounded source/byte comparison, not name or type resolution, a proof check,
or an authentication of external coefficient bytes.

An [independent source review](../../reviews/ordinary14-natural81-recipe-port-bridge-independent/README.md)
checks the bounded import and endpoint signatures without running Lean.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary14-natural81-recipe-port-bridge-draft/check_source.py | cmp - research/ordinary14-natural81-recipe-port-bridge-draft/result.json
```
