# Independent review: corrected child lexical inventory

The [bounded inventory](../../research/ordinary13-independent-k-corrected-lexical-inventory/README.md) reproduces at the pinned bytes. Independent reindexing of its stated local filename scope confirms 821 selected names: 691 selections from the earlier fixed85 JSON plan, 129 single-byte-class selections, and the explicit corrected-composition root. None of the reachable baseline selections is one of the nine alternates. Every selected name has one observed candidate in the stated scan scope; the dependency-first ordering covers all selected local imports and has no cycle.

The unresolved frontier comprises 39 Mathlib, four Foundation and three BusyBeaver import names. At the bounded paths documented by the author, all 46 have observed source files. Each BusyBeaver name has 32 observed, byte-identical copies: the named canonical source and 31 `reviews/*/sources` copies. This comparison does not cover other roots, hidden copies, compiled objects or package resolution precedence. The observed frontier files are not selected providers and their transitive imports are not traversed.

The checker independently reindexes local candidate names, re-reads imports using a separate line-based pass, compares fixed85 source pins and selections, hashes the bounded frontier copies, and checks the dependency order. Like the author's scanner it is **not a Lean parser** and does not establish actual source selection, source/object correspondence, toolchain identity, proof replay, axiom reports or iPRA/PDF equivalence. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B reviews/ordinary13-independent-k-corrected-lexical-inventory-independent/check.py | cmp - reviews/ordinary13-independent-k-corrected-lexical-inventory-independent/receipt.json
```
