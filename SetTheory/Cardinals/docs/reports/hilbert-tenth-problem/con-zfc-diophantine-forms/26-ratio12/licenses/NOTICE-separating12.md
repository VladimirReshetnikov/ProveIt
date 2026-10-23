# Provenance and scope

Prepared for Vladimir Reshetnikov, 22 October 2026, as an AI-assisted research
contribution for the ProveIt repository. The new work is the weighted-root
reduction, the signed-scale refinement and its integer variants, and the
refined finite coefficient compiler, with the accompanying exposition and
verification programs.

The source comparison and copied repository files are pinned to
`VladimirReshetnikov/ProveIt@f0ae4e0991ca44a7bb4e5671d42e33d775e48035`.
The copied files retain their original historical notices; some refer to
earlier snapshots used in their original audits. `SOURCE_MANIFEST.json`
records the current retrieval paths and byte identities.

The ProveIt license and the included third-party Wade license are preserved
in `licenses/`. `upstream/` contains unchanged source material. The 27-integer
builder transforms the explicitly identified source arithmetic packets in
`code/inputs/`; those originals are preserved unchanged. The new material is
provided for incorporation under the repository's MIT No Attribution license.

The mathematical theorems are ordinary proofs formalizable in ZFC. The new
Diophantine reductions and coefficient adapter have not been kernel checked.
The two copied proof-assistant logs are historical upstream evidence for the
machine endpoint, not fresh compilation logs generated for this report.
The finite Python checks do not establish any unbounded consistency claim.

All four giant coefficient ports must be bound to the same complete recipe.
The recipes define exact integers; they are not unknowns or extra quantified
parameters. The emitted arithmetic circuits have no hidden integer registers:
each register is an explicitly substituted polynomial abbreviation.
