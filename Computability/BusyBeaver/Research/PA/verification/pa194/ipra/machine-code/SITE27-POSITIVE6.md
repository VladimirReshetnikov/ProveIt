# PA194 site-27 selected-register positive decision

`PA194Site27SecondRoot.site27SecondRoot` composes the prior six-register
scan/rewind with a state-16 scan and controller return to a second root.
`PA194Site27To1.site27To1` executes the next controller prefix to state 1.
`PA194Site27CarryTo4.carryTo4` scans the arbitrary-length header and uses the
existing six-block carry engine to reach state 4 at the selected physical
register. `PA194Site27To4.site27To4` composes this from the original site-27
header. The selected physical slot 6 is logical register 0.

`PA194Site27PositiveTo6.site27PositiveTo6` assumes only `e 0 = m+1` and
executes the actual state-4 positive row, reaching state 6. All other source
registers, the complete suffix, and model-valued lengths remain arbitrary;
the tape halves and clock are explicit. The module also gives the generic
zero and positive rows, but the full branches have not been returned to their
destination frames.

`check-site27-positive6.sh` rebuilds these nine modules in a fresh suffix
overlay against the five earlier input overlays documented in
`TWO-HEADER-PASSES.md`. The input overlays must have an independently audited
coherent transitive import closure; matching direct object hashes alone does
not establish that closure. `PA194_TWO_PASSES_SOURCE_DIR` can point to an
external source directory. These are all-model semantic execution theorems,
not yet native iPRA derivations or a complete source-step simulation.
