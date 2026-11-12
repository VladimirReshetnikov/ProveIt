# Corrected natural-79 reflection: bounded provider projection

This packet projects the existing 195-module natural-79 overlay with the
[slim client alternative](../ordinary14-natural79-dvd-reflection-slim-draft/README.md)
and the independently prepared [corrected helper](../ordinary14-natural79-slim-reflection-import-repair/README.md).
It checks that the helper adds exactly the explicit
`Foundation.FirstOrder.Arithmetic.IOpen.Basic` import and that the client makes
exactly its two original replacements. The original files and receipts remain
unchanged; no combined overlay is materialized.

The same lexical stopping rule as the previous slim projection gives **five**
missing project-source candidates, **41** selected-P72 project frontier objects,
and **six** external import names. The five candidates and 41 frontier records
are byte-for-byte the same as the previous slim receipt. The only additional
external name is `Foundation.FirstOrder.Arithmetic.IOpen.Basic`.

At observation time its `.olean` was present through the guarded `package-lib`
Foundation symlink (SHA-256
`fdf05f04ff241ddea16128e1fc799cc5cc9470fbc1a63c92a200688ee597ef45`),
and the retained source was present with SHA-256
`4ec52a7a487aeafb0e9ea10716452b34f138d8214ad5a1aa5466064d6a4c9d7b`.
The receipt records selected-root paths, resolved paths, hashes and the observed
same-name companion files. The captured endpoint root and guarded package root
both resolve their Foundation Basic object to the same retained file; these are
provider observations, not proposed output collisions. Source and object hashes
alone do not establish their build relationship or compatibility.

The bounded output-name scan covers **201** prospective names (195 overlay
modules, the helper, and five project source candidates), the same eight
historical roots and 13 suffixes as the earlier natural-79 cut. It finds two
`.olean` observations for `DiophantineConsistency.DiscreteOrderedRingFacts`, in
the captured endpoint and carrier retry roots. These are the two previously
observed locations for that candidate; their existence requires collision-aware
handling, even though neither is the selected-P72 or guarded-package root.
There are no other hits in this specific scan. It does not reserve outputs or
search all possible roots, symlink changes, runtime artifacts, or companions of
the entire dependency tree.

This is source-header and file-presence evidence only. The five candidate
sources are still missing from the selected frontier; this scan does not prove
that their dependencies can be built, authenticate Foundation or Mathlib
producers, establish a complete transitive compiled-import/companion closure,
check the theorem, execute `#print axioms`, or prove the iPRA equivalence. A
future build must independently choose and authenticate its provider roots,
check collisions and resources at execution time, and elaborate the exact
candidate. The physical Carrier65 PDF and its coefficient binding are outside
this projection.

An [independent review](../../reviews/ordinary14-natural79-corrected-reflection-provider-cut-independent/README.md)
checks the revised lexical cut, Foundation observation and bounded collision
scan without establishing Lean resolution or provider compatibility.

From the repository root, while all retained source, package and historical
roots are available, reproduce the observation without invoking Lean:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural79-corrected-reflection-provider-cut/inspect.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural79-corrected-reflection-provider-cut/observation.json
```
