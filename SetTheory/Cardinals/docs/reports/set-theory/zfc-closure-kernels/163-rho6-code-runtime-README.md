# Candidate runtime entry point

Use `run_candidate.py`, or the archive-root `code/reproduce.py --full-runtime`.
The two engine modules are inherited, byte-for-byte pinned sources. Their
historical standalone entry points contain unrelated legacy reconstruction
and regression paths; those entry points are not used by this packet and
their old input trees are not required here.

The supplied candidate driver reads only the explicit table, source JSON,
and adjacent `legacy_mapping.json`. It calls the inherited `prove_blocks`
and `case` functions after mapping native state labels into the engine's
reference labels. The used tape helper operations are pure code (table
parsing, register permutation, and program-counter arithmetic). Imports do
not execute the legacy main functions.

Every case quantifies over independent natural register values and gap,
and an arbitrary nonempty finite spare list. Literal steps, unary-length
induction, and finite-list induction establish whole-tape endpoints and
positive affine durations. The finite construction cap bounds proof search,
not concrete time or represented values.

This is ordinary executable mathematical evidence, not a proof-assistant
kernel certificate. The logical source proof and complete blank startup
are separate obligations, supplied elsewhere in this packet.

Pinned SHA-256:

- symbolic_runtime.py: c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145
- independent_runtime.py: 0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346
- legacy_mapping.json: 26a4bff859adcc510f1faf4364a597681fec014a136bc1d00dc9ce1904ad6bbf

The original authorship and licenses are preserved in the packet notices.
