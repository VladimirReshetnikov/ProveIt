# Adoption into the maintained Lean sources

On26 October2026, `patches/pr-congruence.patch` was integrated into the
maintained `PRCode`, `ScalarPRCode` and `ScalarPROptimizer` modules. Current
source builds, representative clients, compiler checks and executable-value
`rfl` checks pass. The change removes34 proof lines and retains every program
value. The standard-axiom footprint change is documented in the
[iteration review](../../reviews/lean-proof-simplification-20261026-root.md).

The other patches and generated candidates retain their proposal status
until a further adoption entry records their current-source validation.
Original packet files and its archived manifest remain unchanged.
