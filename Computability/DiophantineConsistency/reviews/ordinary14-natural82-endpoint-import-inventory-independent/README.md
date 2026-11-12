# Independent review: natural-82 endpoint import inventory

The [inventory](../../research/ordinary14-natural82-endpoint-import-inventory/README.md) reproduces and accurately describes the checked, bounded source graph. Its 169 bare draft modules form a topological order for the parsed headers, all are reachable from `Natural82Endpoint`, and its 36 directly named qualified project sources exist at the recorded paths with the recorded hashes. This is not a Lean resolver, object-provider, or build-readiness check.

The independent receipt pins the current inventory and the three comparison inventories, reads and hashes every recorded source, and directly parses each initial import header. All 169 current draft headers consist of simple, single-name import commands; the parsed bare and qualified imports match the recorded rows. Each bare import occurs earlier in the order, and its name has a unique `*.lean` candidate **within the research tree**. Each directly qualified name maps to the recorded source under the project's `Lean` directory. These checks do not exclude other candidates in source roots, object roots or Lean's actual search path.

The receipt independently recomputes the root74 and natural86 module and directly qualified-name set differences, as well as the slim overlay comparisons. It confirms the 158 root74-shared original source hashes and the 158 corresponding overlay original-source hashes. It also separately compares the source hashes of all 162 drafts shared with the natural86 snapshot and observes no drift; the original natural86 comparison reports name inclusion and does not itself report that additional hash comparison. The overlay's rewritten source files are not treated as identical to their originals. Its missing-qualified-name comparison includes the intentionally replaced `C44Short15Facts` import and must not be read as a list of missing Lean providers.

The initial-header scan does not follow qualified sources' transitive dependencies, Lean-generated or runtime imports, external packages or toolchain files. It does not establish actual source or object resolution, detect all collisions, inspect provider ancestry and companions, execute `#print axioms`, or prove the natural-82 iPRA endpoint. Reproduction may fail if the shared research tree changes.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural82-endpoint-import-inventory-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural82-endpoint-import-inventory-independent/result.json
```
