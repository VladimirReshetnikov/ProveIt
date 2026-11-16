# PA194 site-27 header and six-register scan

`PA194Site27HeaderPass.site27HeaderPass` proves the first physical
root-to-root header pass from the site-27 prefix. It retains exact model-valued
clock and tape expressions, and allows arbitrary source-register values and
complete suffix. Its input has two leading zero padding cells after the
seven-bit site-27 prefix; the actual startup-derived site-27 frame has 41.

`PA194Site27To106.site27To106` composes the pass with the next eight physical
controller steps to state 106. The encountered state-106 configuration is
not asserted to meet the existing marker theorem's stronger precondition.
`PA194Site27To71.site27To71` then scans the model-length header block and
reaches state 71.

`PA194HalfFileSixWithTail.scanSixExact` generalizes the existing six-block
scan to an arbitrary numeric suffix, retaining each model-valued scan clock,
the exact transformed left half, and a named remaining-file half.
`PA194Site27To14.site27To14` composes this with the state-71 run and reaches
state 14 after scanning the six preceding physical registers. The remaining
right tape includes physical slot 6, which the checked register permutation
maps to logical register 0, and the entire later suffix. This is a bridge
toward the site-27 decrement, not yet its selected-register decision or a
source-step simulation.

`check-site27-to14.sh` rebuilds these ten incremental modules in a fresh
overlay against the five previously checked input overlays described in
`TWO-HEADER-PASSES.md`. It checks selected direct object hashes and the
printed axioms. The input overlays must have an independently audited coherent
transitive import closure; direct object hashes alone do not provide one.
`PA194_TWO_PASSES_SOURCE_DIR` can point to external sources.

These model-uniform execution statements do not themselves constitute an
object-theory iPRA derivation, an all-instruction source simulation, or a
consistency implication.
