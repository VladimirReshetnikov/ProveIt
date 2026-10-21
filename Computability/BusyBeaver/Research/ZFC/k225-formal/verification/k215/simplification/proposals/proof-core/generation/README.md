# Reproducible implication-proof compression and finite schemas

This directory contains the discovery and source-generation evidence for
the new implication proof simplification at ProveIt commit
aa66d0a33f1f8237a348899eb8095b045a502832.

The companion formal-proof export contains the Lean and Rocq sources,
compiler logs, typed client checks, and kernel audit receipts.
This directory is intentionally small: it omits all machine tables,
toolchains, object files, downloaded packets, and failed experiments.

## Replay

Python 3 and its standard library suffice. From this directory:

```sh
python3 generation/regenerate.py --check
python3 generation/search_shortcuts.py
python3 generation/specialize_four.py --check
sha256sum -c SHA256SUMS
```

The first command verifies the exact pinned original source, recomputes
the thirteen selected schematic MP substitutions, audits each instantiated
MP equation, checks acyclic dependencies, and reproduces the final generic
core and compatibility adapter byte for byte.

The second replays the finite single-MP discovery search: 117 existing
helper schemas yield 2,944 ordered replacement possibilities, and all
thirteen selected shortcuts are included. It is not an optimality search.

The third reproduces the four-schema extension, checks the exact output
hash, and inventories all nine guard-witness uses. It preserves the
generic core unchanged. Small source snapshots in generation/ are needed
for these byte-for-byte checks; they duplicate only the corresponding
small formal source files, not the full proof dependency closure.

To generate source files into a new directory:

```sh
python3 generation/regenerate.py --out /path/to/output
python3 generation/specialize_four.py --out /path/to/output
```

The generated layout is BusyBeaver/ZFC/. Copy that directory under
Computability/BusyBeaver/Lean/ in the pinned repository. The separate
numeric KCodeFourShape adapter is in the formal export and the extension
patch. Templates and Python generators are untrusted proof producers.
The Lean and Rocq kernels check the resulting proof terms.

## Files

- FINDINGS.md: proof compression, exact assumptions, direct B/C/K/P
  finishing argument, measurements, existing alternative ranking.
- FOUR_SHAPES.md: strongest new theorem, exact four-schema table, numeric
  CFour equivalence, trust boundary, and state-synthesis limitations.
- generation/shortcuts.json: selected pairs, pinned upstream hash, and
  retained proof roots.
- generation/DomRho8.original.lean: exact attributed upstream source.
- generation/regeneration.json, search-summary.json, four-shapes.json:
  deterministic replay reports.
- generation/templates/: public interfaces, final direct proof, adapter,
  and four-schema specialization interfaces.
- patches/final-integration.patch: generic core plus API-preserving
  replacement for DomRho8.lean.
- patches/four-shape-extension.patch: optional new finite-schema core and
  CFour code-calculus adapter.
- SHA256SUMS: hashes of every delivered file except the manifest itself.

## Exact claims and limits

The compatibility rewrite changes 117 numbered helpers to 84, removes
the auxiliary natural-deduction calculus, and reduces source size from
30,114 bytes to 22,278 bytes across the generic core and adapter.
This measures source text, not proof-object size or full build time.

The generic theorem assumes only a carrier A, implication I, a reflexive
relation closed under insertion in either implication operand, MP, and
restricted rho8. There is no truth, bottom, decoding, injectivity, zero
identity, separate transitivity, or global inhabitedness premise.

The stronger finite-schema theorem assumes only A, I, MP, and the four
explicit rho8 families with first argument u, I(x,u), I(I(u,x),y), or
I(I(I(x,u),y),z). It has no order or relation-closure assumption.
Its generic theorem is checked in both Lean and Rocq. The Lean CFour
adapter retains every other C222 rule, including truth and both bundle
guards, and proves equality of derivability at every raw natural code.

The full primary K215 endpoint was not rebuilt as part of these local
proof checks. No 214-state machine, new compiled source emitter, lower
bound, or minimality theorem follows from this proof compression.
CM215's favorable alternative ranking is inherited from current
repository proposals and is not claimed as a new machine discovery.
