# Natural-80 endpoint lexical inventory and bounded token scan

The unelaborated `Natural80Endpoint.lean` has **184 bare draft modules** in
this source-header traversal and **41 directly named qualified project
sources**. `inventory.json` records each original source path, SHA-256 and
simple initial-header imports in topological order, not Lean's actual
resolved providers. The scan for duplicate bare names covers only `.lean`
files below `Computability/DiophantineConsistency/research`; it does not
rule out competing sources or objects elsewhere. Qualified project source
headers, package imports, compiled objects, runtime dependencies, and actual
Lean search order are not traversed.

An [independent source review](../../reviews/ordinary14-natural80-endpoint-import-inventory-independent/README.md)
checks the lexical closure and bounded token observations without resolving
Lean providers or inspecting axiom closure.

All 173 modules in the pinned natural-81 inventory occur with the same
source hashes, alongside 11 natural-80 additions. The original root74 slim
overlay shares 158 endpoint modules with unchanged original-source hashes,
but lacks the 26 new modules recorded in the JSON. `Root74Endpoint` exists in
that overlay but is not part of this closure. These observations do not create
or certify a combined overlay. Direct qualified-name differences compare
original headers with intentionally rewritten slim headers and therefore do
not identify a resolved provider cut.

`scan_tokens.py` checks hashes of the 184 drafts and 41 directly named source
files and performs the same bounded comment/string-scrubbed lexical token
scan used by the root74 proof-escape audit. It finds 15 standalone `partial`
tokens in two predecessor draft sources; these appear to be uses of a helper
named `partial`, not evidence of `partial def` or a proof escape. The
[separate parser-source warning and inert alternatives](../ordinary14-natural-partial-keyword-patch/README.md)
explain a potential syntax hazard, unconfirmed by Lean. No other tokens in
its listed escape set are observed. The scan also finds five explicit
`Classical.choose`/`Classical.choice`-family references in three direct
qualified sources and 314 `#print axioms` source commands. These are source
observations: the commands were not executed; neither choice references nor
their absence prove the endpoint's axiom closure.

The scanner is not a Lean parser: it handles nested comments, line comments
and ordinary strings, rejects selected unsupported literal forms and quoted
identifiers, and may not recognize other Lean syntax. Its inputs omit
transitive qualified sources, package/toolchain providers, generated code,
object companions and tactic behavior. No Lean elaboration, proof existence,
physical coefficient/PDF binding, or safe build plan follows from the scan.
The uncompiled predecessor-order alternatives are not included: the inventory
records the original `.lean` sources currently imported by the draft chain.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural80-endpoint-import-inventory/check_source.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural80-endpoint-import-inventory/inventory.json
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural80-endpoint-import-inventory/scan_tokens.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural80-endpoint-import-inventory/tokens.json
```
