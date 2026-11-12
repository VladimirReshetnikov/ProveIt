# Independent review: natural-80 endpoint source inventory

The [inventory and bounded token scan](../../research/ordinary14-natural80-endpoint-import-inventory/README.md) reproduce and support the documented source-level observations. They do not resolve actual Lean imports, establish an axiom closure or provider provenance, elaborate the endpoint, or prove an iPRA or physical-file result.

The independent receipt rehashes all 184 listed draft sources and 41 directly named qualified project files. It reads the actual simple initial import headers, verifies their recorded topological order and endpoint reachability, and compares the 173 shared natural-81 original-source hashes plus the 158 shared root74 slim original-source hashes. It confirms 11 added drafts relative to the natural-81 snapshot and 26 drafts outside the original root74 slim overlay. These are source-set comparisons; they do not construct a combined build or identify a resolved provider cut. This independent receipt does not reproduce the candidate's research-tree-wide duplicate-name search.

A separate bounded comment/string scrubber confirms the recorded 15 `partial` token occurrences in the two predecessor sources, five `Classical` selection references, and 314 unexecuted `#print axioms` commands across the 225 checked files. No other token from the enumerated escape list appears under that restricted scanner. The `partial` declaration has a separately documented [likely parser hazard](../../research/ordinary14-natural-partial-keyword-patch/README.md); no Lean run has confirmed it. The token scan is not a general Lean lexer or proof-escape detector. The presence or absence of particular tokens and unexecuted axiom commands does not determine theorem axiom closure.

The scan omits transitive qualified sources, package and toolchain objects, companions, generated code and tactic or runtime behavior. Its finite source checks do not establish safe provider reuse or prove that the iPRA equivalence exists.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural80-endpoint-import-inventory-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural80-endpoint-import-inventory-independent/result.json
```
