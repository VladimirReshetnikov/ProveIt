# Independent static audit of the joint 13-variable manifest

This static review passed with actual process exit 0, recorded in
[terminal-observation.json](terminal-observation.json). The [receipt](receipt.json)
pins the eight source modules, their Git blobs at `72bb86f994`, the guarded
manifest and the audited historical parent manifest. It checks all eight
source hashes and declared import lists, their topological order and absence
of parent shadowing, and the exact 13 ordered diagnostic names. The declared
imports have 11 direct parent edges and eight direct addition edges; traversal
finds 1,096 parent modules in their declared transitive closure. External
module names are recorded but their transitive or dynamic ancestry is not
established by this static survey.

The review independently parses and matches all 13 variable indices, four
port indices, 87 sum-of-squares operations and 86 product operations to their
pinned Lean literal bodies. Three mutations per graph are rejected. It checks
the sum-of-squares native and standard endpoint statements and the product
native and standard statements, including the product's positive shift and
both selected Gödel–Gentzen-translated Foundation consistency sentences.
These are checked source statements, not a new Lean compilation or a formal
interpretation of either PDF.

Five malformed source/metadata mutations are rejected by the actual generic
guarded runner's source validator, and four task-policy mutations are rejected
by this review's exact list and fixed manifest digest. There is an important
scope distinction: the generic validator intentionally accepts a structurally
valid report list with one name removed. The task-specific list is protected by
the independently fixed manifest SHA-256 supplied to the runner, and the
runner later compares actual compiled reports with that pinned list. A caller
who changes both the manifest and the externally supplied digest has changed
the policy being authorized; the generic validator alone does not prevent it.

This review does **not** claim the guarded run has occurred or succeeded, a
matched replay, current-source provenance, formal PDF semantics, or complete
package-transitive/dynamic ancestry. Parent snapshot drift and the unobserved
Foundation wrapper outer-exit limitation remain. The manually transcribed
PDF decoder/table/rank/port recipe boundary also remains.

Run with ordinary Python after preserving and moving aside only this packet's
receipt:

```sh
python3 Computability/DiophantineConsistency/reviews/ipra-standard-13-frontier-static-independent-audit/audit.py
```

It needs the pinned historical parent snapshot and source Git commit, refuses
to overwrite its receipt and rejects optimized Python.
