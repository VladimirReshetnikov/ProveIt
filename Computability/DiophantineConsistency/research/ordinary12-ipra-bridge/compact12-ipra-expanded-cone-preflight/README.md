# Expanded native endpoint reverse-impact cone

`analyze.py` follows the recorded selected-project serialized imports from
`IPRAExpressionNative`, `HAExpressionAssembly` and
`AdaptiveEquationSyntax2011`. Their union contains 863 selected project
objects; 44 are byte-conflicting selection seeds, 366 are affected objects
selected from the nine provider, and 59 are the previously omitted affected
objects. The conservative candidate rebuild is therefore 425 objects. The
file `result-v2.json` contains the full dependency-ordered candidate list,
selected-object and source hashes/paths, endpoint seed conflict pairs,
source-import comparisons, and ancestor lists for all three endpoint roots
and the compact symbolic model theorem. `PositiveModelIPRAAdapter` itself
is not in the selected overlay: its checked source imports the first three
roots, but its separate serialized object was not included in this graph.
The compact symbolic theorem's selected graph contains zero nine-selected
affected objects; that is not a full provider ancestry audit.

All 425 candidate modules have one current canonical workspace source in the
seven listed Lean roots, with hashes recorded. Their parsed direct imports
within this selected-object graph match the serialized object imports. This
is an import-shape comparison only: it does not authenticate the current
source as the historical origin of an existing object. The first uncommitted
analysis `result.json` used only five source roots and reported five missing
sources; those canonical FirstOrder and ZF roots were located and added for
`result-v2.json`. Both observations are preserved.

Every earlier stage 1–15 has 8–18 affected nine-selected ancestors. Those
stages compiled against the earlier overlay but must be treated as
**provisional** for the enlarged coherent build and rebuilt after their
changed predecessors, or justified by a stronger independent compatibility
argument. They are not an iPRA endpoint. Topological order covers the recorded
selected-object direct imports only; package, dynamic and other missing
ancestry remain separate checks. The 425 historical object files occupy
214,106,944 bytes (about 204 MiB); the first 15 new objects occupied about
7.8 MiB. These are planning measurements, not a bound on build peak disk use,
companion files, logs, memory, or future object sizes.

Current `analyze.py` SHA-256
`7ab2f9d39e5d35dee8372a2b8ccb1c16706611fa6ec43548b15926947ac70a11`;
`result-v2.json` SHA-256
`35fce2dd6720ca1f2db8c39e42ad099f5653bf6b12939fcb77db3fd0fa252ed4`.
The full-scan input SHA-256 is
`bf812db57d68117d47d3df792e4a0d6879019d442c4f0f2b0fbef8b861f363f2`.
