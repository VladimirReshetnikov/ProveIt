# Bounded root74 draft namespace and API audit

This source-only lexical audit checks the 159 bare draft modules in the pinned
root74 endpoint inventory. After removing nested comments, line comments and
ordinary strings, it finds 842 occurrences of references of the lexical form
`NamespaceDraft.declaration` (581 distinct consumer/namespace/declaration
triples). In this bounded scan each named declaration has a unique recorded
draft namespace provider, that provider is reachable through the consumer's
bare import closure, and no external reference names a declaration marked
`private`. The receipt lists source hashes and every reference with line number.

These checks are deliberately narrow. The namespace scanner is not Lean's
parser or elaborator: it approximates declarations using the first matching
`*Draft` namespace in a file. It does not establish resolution of unqualified
names, notation, instances, implicit arguments, overloaded names, macros,
quoted identifiers or package/Foundation dependencies. A recorded textual
name and import path do not prove a type checks. A separate audit records two
unresolved lexical tactic-import paths; neither absence nor an observed Lean
failure follows from that search.

The checker also verifies exact source snippets for the P72 cast/subtraction
interfaces, the signed-pair product unit extractor, the internal negative-Pell
exclusion and the three iPRA adapter interfaces. `ArithmeticSignedPairs` is a
separately hash-pinned transitive source, not a direct qualified inventory
entry. Two in-memory mutation controls remove a named provider and a root import
and confirm those defects would be noticed by the bounded checks. No source is
modified by the checker.

Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-root74-draft-api-audit/check_source.py | cmp - research/ordinary14-root74-draft-api-audit/observation.json
```

No Lean run, theorem or axiom verification, transitive provider closure,
launch readiness, model/iPRA endpoint or byte/PDF binding is claimed.

Independent source review: [root74 draft API audit](../../reviews/ordinary14-root74-draft-api-audit-independent/README.md).
