# Adoption into the maintained Lean sources

On26 October2026, `patches/pr-congruence.patch` was integrated into the
maintained `PRCode`, `ScalarPRCode` and `ScalarPROptimizer` modules. Current
source builds, representative clients, compiler checks and executable-value
`rfl` checks pass. The change removes34 proof lines and retains every program
value. The standard-axiom footprint change is documented in the
[iteration review](../../reviews/lean-proof-simplification-20261026-root.md).

`patches/assignment-map.patch` is also integrated in `Representation`, and
the quartic compiler reuses its shared assignment lemma. The two modules
and representative constructor/size/cost clients pass current-source Lean
checks. Together they remove26 lines, preserving witness and expression data.

`patches/list-library.patch` is integrated in the five Annotated checker
modules. All five module builds, four direct clients and five existing
focused checks pass. Seven private wrappers now reuse the core list API,
removing40 lines while preserving every wrapper signature and checker value.

The other patches and generated candidates retain their proposal status
until a further adoption entry records their current-source validation.
Original packet files and its archived manifest remain unchanged.
