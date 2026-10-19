# Exact baseline, inherited inputs, and attribution

Prepared 18 October 2026 for the ProveIt project in response to the request
for fewer than 243 working states.

## Baseline revision

ProveIt repository:
<https://github.com/VladimirReshetnikov/ProveIt>

Pinned revision: `e58338db7545909907e07a7603e8eb88625c527a`.

The exact predecessor is
`Computability/BusyBeaver/Research/ZFC/candidate-combined243/` at that revision.
Its README, reproduction instructions, ordinary comparison, and inherited
table are retained in `reference/`. Its canonical table hash is
`a3860fb49d6b96e58ead6293134f246d59b3958231cb56850273c4b8a8138791`.
Its inherited-label table hash is
`4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300`.

The maintained README explicitly supports the ordinary statement
`ZFC ⊢ (¬Halt(Combined243) ↔ Con(ZFC))`, distinguishes its relative Lean
theorem from a complete consistency endpoint, and records the latter as
still open. Detour242 transports the ordinary statement with a newly proved
relative equivalence. It does not silently upgrade any inherited formal
endpoint.

## Runtime reference

The unchanged checker dependency tree in `reference/baseline245/` comes from
the retained source-71 QT loop-rotation contribution, using its original
`reference/baseline245/` subtree. The selected dependency index
`reference/reference-inputs.json` pins all 291 supplied files. The source
rotation and literal-checker originals in `reference/rotation244/` are
retained for attribution and reproducibility; the new candidate adapters
are separate files in `code/`.

The exact rotated source is unchanged from Combined243: 6,459 leaves and
8,390 guarded instruction cases. Logical-list SHA256:
`3ee984818f0bdfd2c4daae72aeb14340572e34d73f5cdb5616b6d29d78fcd7f4`.

## New machine identity

Canonical table SHA256:
`ef8c07f372c76a73c021f51801f16f28f1e4ca5ead2d4ce6780c2a245a0db245`.

Inherited table SHA256:
`c8ef2f44d25fee6813164cc59ec05061799397da8cf7f0ea7baab63d32d76e02`.

The novel patch deletes inherited state 27 and changes precisely retained
rows 15/0, 18/0, 47/0 and 65/0. The construction script reproduces complete
byte strings, including terminal newlines. The local proof and independent
audit both check the exact predecessor rather than a nominal state count.

## Alternative formalism

The equational reference is source 70 / intake 166 at the same revision,
under `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/`:

- `data/70-c244-equational-reference-FC13B_complete.json`;
- `data/70-c244-equational-grouped.json`;
- `code/70-c244-equational-build_equations.py`;
- `code/70-c244-equational-equational_search.py`.

The transformation and new exact packet are in
`research/equational1768/`. The ordinary model proof is relative to the
inherited complete FC13B/equational calibration. There is no binary-machine
state estimate for this packet.

## Attribution and notices

The original calculus/program, verification and compiler remain credited to
Mira-Cult, Jeff Ketchersid and Andrew James Wade, following the maintained
ProveIt attribution. The source, routing, initialization, compensated fold,
QT rotation and their predecessor reviews remain credited to their existing
contributions. This package claims only the new detour reduction, its proof,
new verification runs, the documented search work and the separate
equational transformations.

Inherited license files and notices are retained in the reference tree,
including `LICENSE.ProveIt`, `LICENSE.Wade`, and upstream attribution notes.
Do not replace them with an inferred personal authorship attribution.

The upstream user-supplied prior art is:

- <https://wiki.bbchallenge.org/wiki/Logical_independence>;
- <https://github.com/jeff87654/busy-beaver/tree/zf-254/ZF/m254>.

The report cites the primary Sheffer-basis paper used by the inherited
equational backend. This packet does not claim authorship of that basis.
