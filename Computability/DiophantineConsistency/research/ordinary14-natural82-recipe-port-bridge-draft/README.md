# Natural-82 closed recipe-port client: source proposal

`Natural82RecipePorts.lean` is an **unelaborated source-only client** of the
[natural-82 endpoint draft](../ordinary14-natural-forced82-ipra-draft/README.md).
It proposes rewriting the graph's symbolic port tuple to `byteP` using the
existing `CompactBytePortsModelIff.byteP_eq` declaration, then transporting
its proposed polynomial bridge and native, standard, and equality-only iPRA
endpoints. This client is a mechanical adaptation of the existing
[natural-86 recipe-port client](../ordinary14-natural86-recipe-port-bridge-draft/README.md),
with an explicit `HAExpressionAssembly` namespace opening for
`PolynomialBridge` and five `#print axioms` commands added for a future
build. The commands have not run and provide no axiom evidence.

`byteP` decodes closed lists defined in Lean; this proposal does not prove that
those lists equal external P72/P115 files or that either expression describes
the different Carrier65 equation in the current PDF. The client, imports,
rewrites, endpoint chain, providers and the iPRA theorem remain unelaborated
and unverified. See the [physical binding audit](../ordinary14-natural82-86-physical-binding-audit/README.md)
for the distinct file and displayed-page obligations.

The read-only source checker pins both client texts, the endpoint and the
byte-port declaration, and checks that this adaptation is exact and contains
the proposed axiom commands. It does not run Lean, resolve imports, check
semantics or compare physical file bytes.

An [independent source review](../../reviews/ordinary14-natural82-recipe-port-bridge-independent/README.md)
checks the declared rewrite, client signatures and explicit namespace opening;
it does not establish elaboration or axiom closure.

Run from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary14-natural82-recipe-port-bridge-draft/check_source.py | cmp - research/ordinary14-natural82-recipe-port-bridge-draft/result.json
```
