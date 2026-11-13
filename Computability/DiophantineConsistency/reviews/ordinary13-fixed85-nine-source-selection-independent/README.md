# Independent review: nine-alternative fixed-85 source selection

The plan and author receipt reproduce. The independent checker rehashes all
1,354 selected sources, reparses their lexical imports, and confirms each
non-overridden selection matches the pinned baseline path, hash and imports.
It checks these exact nine logical names against the separately recorded
alternative paths and hashes:

```
ResidueSignFreePower          ResidueRankLower
ResidueExactIndexWitness      ResidueExactIndexModel
Residue90FyForce              AQ17Forced105Arithmetic
Residue90FirstNormGap         Residue90CompactGraphGamma
Residue90GammaModel
```

All nine namespace declarations match their historical selected sources;
the one selected path for each name is the intended inert alternative, not
its original provider. The 1,354 virtual logical `.lean` labels and selected
source paths are unique **within this JSON selection**. These checks do not
change a Lean search path or establish that a renamed `.lean.src` file has
actually been installed under its logical name.

Independently traversing the selected lexical imports from `Fixed85Endpoint`
reaches all 1,354 selected modules and 93 external/frontier names. The only
removed baseline frontier name is `Mathlib.Tactic.Omega`; this does not rule
out other Omega imports within unscanned external sources. The recorded order
is dependency-first on selected local edges, with no local cycle; a separate
reverse traversal from all nine alternatives reaches 55 selected locals,
including the endpoint. It is a bounded source-dependency set rather than an
authenticated rebuild order or complete transitive closure.

The plan accurately limits its claims: it selects no external package or
compiled object, does not search all competing source/object roots, and does
not authenticate imports, source/olean identity, dynamic libraries, axiom
boundaries, available disk or any Lean theorem. A future isolated environment
must realize each logical mapping and prevent duplicate historical providers.
No concrete source-selection mismatch was found; the nine proposed proof
scripts still need their own reviews and Lean validation.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-fixed85-nine-source-selection-independent/check.py | cmp - reviews/ordinary13-fixed85-nine-source-selection-independent/receipt.json
```
